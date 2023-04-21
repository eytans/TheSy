use crate::egg::tools::tools::Grouped;
use egg::appliers::DiffApplier;
use egg::reconstruct::reconstruct_all;
use egg::{Analysis, Applier, ColorId, EGraph, Id, Language, Pattern, Runner, SearchMatches, Searcher, StopReason, SymbolLang, Iteration};
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use smallvec::alloc::fmt::Formatter;
use std::collections::hash_map::RandomState;
use std::fmt;
use std::fmt::Debug;
use std::rc::Rc;
use std::time::Duration;

use crate::lang::{ThEGraph, ThRewrite};
use crate::thesy::statistics::{sample_graph_stats, StatsReport};
use egg::tree::Tree;
use serde::{Deserialize, Serialize};
use std::str::FromStr;

/// To be used as the op of edges representing potential split
pub const SPLITTER: &'static str = "potential_split";
lazy_static! {
    /// Pattern to find all available splitter edges. Limited arbitrarily to 5 possible splits.
    pub(crate) static ref SPLIT_PATTERNS: Vec<Pattern<SymbolLang>> = {
        vec![
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1)", SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2)", SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2 ?c3)", SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2 ?c3 ?c4)", SPLITTER)).unwrap(),
        ]
    };
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct Split {
    root: Id,
    splits: Vec<Id>,
    color: Option<ColorId>,
}

impl Split {
    pub fn new(root: Id, splits: Vec<Id>, color: Option<ColorId>) -> Self {
        Split {
            root,
            splits,
            color,
        }
    }

    pub fn color(&self) -> Option<ColorId> {
        self.color
    }

    pub(crate) fn update(&mut self, egraph: &ThEGraph) {
        self.root = egraph.opt_colored_find(self.color, self.root);
        for i in 0..self.splits.len() {
            self.splits[i] = egraph.opt_colored_find(self.color, self.splits[i]);
        }
    }

    pub fn create_colors<L: Language, N: Analysis<L>>(
        &self,
        egraph: &mut EGraph<L, N>,
    ) -> Vec<ColorId> {
        egraph.rebuild();
        self.splits
            .iter()
            .map(|id| {
                let c = if let Some(base_color) = self.color {
                    egraph.create_sub_color(base_color)
                } else {
                    egraph.create_color()
                };
                let fixer = |id: Id| egraph.get_color(c).unwrap().translate_from_base(id);
                egraph.colored_union(c, fixer(self.root), fixer(*id));
                egraph.rebuild();
                c
            })
            .collect_vec()
    }

    pub fn by_translation(&self, trns: &IndexMap<Id, Tree>) -> String {
        let root = trns
            .get(&self.root)
            .map(|x| x.to_string())
            .unwrap_or("No reconstruct".to_string());
        let splits = itertools::Itertools::intersperse(
            self.splits.iter().map(|c| {
                trns.get(c)
                    .map(|x| x.to_string())
                    .unwrap_or("No reconstruct".to_string())
            }),
            " ".to_string(),
        )
        .collect::<String>();
        let color = format!("{:?}", self.color);
        return format!("(root: {}, splits [{}], color: {})", root, splits, color);
    }
}

impl fmt::Display for Split {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(root: {}, splits [{}], color: {})",
            self.root,
            itertools::Itertools::intersperse(
                self.splits.iter().map(|x| usize::from(*x).to_string()),
                " ".parse().unwrap()
            )
            .collect::<String>(),
            self.color
                .map(|c| usize::from(c).to_string())
                .unwrap_or("None".to_string())
        )
    }
}

pub type SplitApplier = Box<dyn FnMut(&mut ThEGraph, Vec<SearchMatches>) -> Vec<Split>>;

/// A struct to collect statistics to
#[cfg(feature = "stats")]
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct CaseSplitStats {
    pub(crate) vacuous_cases: Vec<usize>,
    pub(crate) known_splits_text: IndexSet<String>,
    pub iterations: Vec<Vec<Iteration<()>>>,
}

#[cfg(feature = "stats")]
impl CaseSplitStats {
    pub fn new() -> Self {
        CaseSplitStats {
            vacuous_cases: vec![],
            known_splits_text: Default::default(),
            iterations: vec![],
        }
    }
}

pub struct CaseSplit {
    splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, SplitApplier)>,
    #[cfg(feature = "stats")]
    pub stats: CaseSplitStats,
}

impl Debug for CaseSplit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "CaseSplit {{ splitter_rules: {:?} }}",
            self.splitter_rules
                .iter()
                .map(|(s, _)| (s.to_string(), "TODO print applier"))
                .collect_vec()
        )
    }
}

impl CaseSplit {
    pub fn new(splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, SplitApplier)>) -> Self {
        CaseSplit {
            splitter_rules,
            #[cfg(feature = "stats")]
            stats: Default::default(),
        }
    }

    pub fn from_applier_patterns(
        case_splitters: Vec<(
            Rc<dyn Searcher<SymbolLang, ()>>,
            Pattern<SymbolLang>,
            Vec<Pattern<SymbolLang>>,
        )>,
    ) -> CaseSplit {
        let res = CaseSplit::new(
            case_splitters
                .into_iter()
                .map(|(searcher, pattern, split_evaluators)| {
                    let diff_pattern = DiffApplier::new(pattern);
                    let applier: SplitApplier =
                        Box::new(move |graph: &mut ThEGraph, sms: Vec<SearchMatches>| {
                            let mut res = vec![];
                            for sm in sms {
                                for subst in &sm.substs {
                                    // ECLass is irrelevant
                                    let id = diff_pattern.apply_one(graph, sm.eclass, subst);
                                    assert_eq!(id.len(), 1);
                                    res.push(Split::new(
                                        id[0],
                                        split_evaluators
                                            .iter()
                                            .map(|ev| ev.apply_one(graph, sm.eclass, &subst)[0])
                                            .collect_vec(),
                                        subst.color(),
                                    ));
                                }
                            }
                            res
                        });
                    (searcher.clone(), applier)
                })
                .collect_vec(),
        );
        res
    }

    pub fn extend(&mut self, other: Self) {
        self.splitter_rules.extend(other.splitter_rules)
    }

    // TODO: can this be an iterator?
    fn split_graph(egraph: &ThEGraph, split: &Split) -> Vec<ThEGraph> {
        split
            .splits
            .iter()
            .map(|child| {
                let mut new_graph = egraph.clone();
                new_graph.union(split.root, *child);
                new_graph
            })
            .collect_vec()
    }

    fn equiv_reduction(&mut self, rules: &[ThRewrite], egraph: ThEGraph, run_depth: usize) -> ThEGraph {
        let mut runner = Runner::default()
            .with_time_limit(Duration::from_secs(60 * 10))
            .with_node_limit(egraph.total_number_of_nodes() + 200000)
            .with_egraph(egraph)
            .with_iter_limit(run_depth);
        runner = runner.run(rules);
        match runner.stop_reason.as_ref().unwrap() {
            StopReason::Saturated => {}
            StopReason::IterationLimit(_) => {}
            StopReason::NodeLimit(_) => {
                warn!("Stopped case split due to node limit")
            }
            StopReason::TimeLimit(_) => {
                warn!("Stopped case split due to time limit")
            }
            StopReason::Other(_) => {}
        };
        // info!("Runner finished, rebuilding");
        // info!("Iterations: ");
        // for i in runner.iterations {
        //     info!("  apply time: {}", i.apply_time);
        //     info!("  search time: {}", i.search_time);
        //     info!("  rebuild time: {}", i.rebuild_time);
        //     info!("");
        // }
        runner.egraph.rebuild();
        #[cfg(feature = "stats")]
        self.stats.iterations.push(std::mem::take(&mut runner.iterations));
        runner.egraph
    }

    pub fn find_splitters(&mut self, egraph: &mut ThEGraph) -> Vec<Split> {
        debug!("Finding splitters");
        let mut res = vec![];
        for (s, c) in &mut self.splitter_rules {
            res.extend(c(egraph, s.search(egraph)));
            egraph.rebuild();
        }
        res.iter_mut().for_each(|x| x.update(egraph));
        debug!("Found {} splitters", res.len());
        res.into_iter().unique().collect()
    }

    fn merge_conclusions(
        egraph: &mut ThEGraph,
        color: Option<ColorId>,
        classes: &Vec<Id>,
        split_conclusions: &Vec<IndexMap<Id, Id>>,
    ) {
        let mut group_by_splits: IndexMap<Vec<Id>, IndexSet<Id>> = IndexMap::new();
        for c in classes {
            let key = split_conclusions.iter().map(|m| m[c]).collect_vec();
            group_by_splits.entry(key).or_default().insert(*c);
        }
        for group in group_by_splits.values().filter(|g| g.len() > 1) {
            // print group and reconstruct each member
            debug_assert!(
                group
                    .iter()
                    .filter_map(|id| egraph[*id].color())
                    .unique()
                    .count()
                    <= 1
            );
            // TODO: might need to look into hierarchical colors conclusions.
            // TODO: What about split conclusion from only colored matches?
            if group.len() > 1 {
                debug!("\tMerging group: {:?} for color {:?}", group, color.clone());
            }
            let mut it = group.iter();
            let mut res = *it.next().unwrap();
            for id in it {
                res = egraph.opt_colored_union(color.clone(), res, *id).0;
            }
        }
        egraph.rebuild();
    }

    fn collect_merged(egraph: &ThEGraph, classes: &Vec<Id>) -> IndexMap<Id, Id> {
        classes
            .iter()
            .map(|c| (*c, egraph.find(*c)))
            .collect::<IndexMap<Id, Id>>()
    }

    fn collect_colored_merged(
        egraph: &ThEGraph,
        classes: &Vec<Id>,
        color: ColorId,
    ) -> IndexMap<Id, Id> {
        classes
            .iter()
            .map(|eclass| {
                let fixed = egraph
                    .get_color(color)
                    .unwrap()
                    .translate_to_base(egraph.colored_find(color, *eclass));
                (*eclass, fixed)
            })
            .collect::<IndexMap<Id, Id>>()
    }

    pub fn case_split(
        &mut self,
        egraph: &mut ThEGraph,
        split_depth: usize,
        rules: &[ThRewrite],
        run_depth: usize,
    ) {
        if !cfg!(feature = "no_split") {
            info!("Case splitting with depth {}", split_depth);
            if cfg!(feature = "split_clone") {
                let mut vacuity_cases = 0;
                if cfg!(feature = "keep_splits") {
                    self.keep_splits_case_split(
                        egraph,
                        split_depth,
                        &Default::default(),
                        rules,
                        run_depth,
                        &mut vacuity_cases,
                    );
                } else {
                    self.inner_case_split(
                        egraph,
                        split_depth,
                        &Default::default(),
                        rules,
                        run_depth,
                        &mut vacuity_cases,
                    );
                }
                if !cfg!(feature = "optimized_split_behaviour") {
                    *egraph = self.equiv_reduction(
                        rules,
                        std::mem::take(egraph),
                        split_depth * run_depth,
                    );
                }
                info!("Found {} vacuity cases", vacuity_cases);
                sample_graph_stats(egraph, StatsReport::CaseSplitDepth(split_depth));
                self.stats.vacuous_cases.push(vacuity_cases);
            } else {
                let mut map = IndexMap::default();
                let initial_vacuos = egraph.detect_color_vacuity();
                // Hack to not fail first checks
                map.insert(None, Default::default());
                self.colored_case_split(egraph, split_depth, map, rules, run_depth);
                self.stats.vacuous_cases.push(
                    egraph
                        .detect_color_vacuity()
                        .iter()
                        .filter(|x| !initial_vacuos.contains(x))
                        .count(),
                );
            }
        }
    }

    fn colored_case_split(
        &mut self,
        egraph: &mut ThEGraph,
        split_depth: usize,
        mut known_splits_by_color: IndexMap<Option<ColorId>, IndexSet<Split>>,
        rules: &[ThRewrite],
        run_depth: usize,
    ) {
        if split_depth == 0 {
            return;
        }
        debug!("Colored Case splitting with depth {}", split_depth);
        let color_keys = known_splits_by_color.keys().cloned().collect_vec();
        for color in color_keys {
            let mut splits = known_splits_by_color.remove(&color).unwrap();
            splits = splits
                .into_iter()
                .map(|mut split| {
                    split.update(egraph);
                    split
                })
                .collect();
            known_splits_by_color.insert(color, splits);
        }

        let temp = self.find_splitters(egraph);
        for s in &temp {
            let trns = reconstruct_all(egraph, s.color, 4);
            debug!(
                "  {} - root: {}, cases: {}",
                s,
                trns.get(&s.root)
                    .map(|x| x.to_string())
                    .unwrap_or("No reconstruct".to_string()),
                itertools::Itertools::intersperse(
                    s.splits.iter().map(|c| trns
                        .get(c)
                        .map(|x| x.to_string())
                        .unwrap_or("No reconstruct".to_string())),
                    " ".to_string()
                )
                .collect::<String>()
            );
        }
        let temp_len = temp.len();
        let mut splitters: Vec<Split> = temp
            .into_iter()
            .filter(|s| {
                known_splits_by_color.contains_key(&s.color)
                    && !known_splits_by_color[&s.color].contains(s)
            })
            .collect();
        warn!(
            "Splitters len (in depth {split_depth}, orig len: {temp_len}): {}",
            splitters.len()
        );
        warn!(
            "Splittes use colors: {:?}",
            splitters.iter().map(|s| s.color.as_ref()).counts()
        );
        for s in splitters.iter_mut() {
            known_splits_by_color[&s.color].insert(s.clone());
            if let Some(c) = s.color {
                for child in egraph.get_color(c).unwrap().children() {
                    let mut new_s = s.clone();
                    new_s.color = Some(*child);
                    new_s.update(egraph);
                    known_splits_by_color[&Some(*child)].insert(new_s);
                }
            }
        }

        egraph.rebuild();
        let classes = egraph.classes().map(|c| c.id).collect_vec();
        let colors = splitters
            .iter()
            .map(|s| (s.color.clone(), s.create_colors(egraph)))
            .collect_vec();
        for (_, cs) in &colors {
            for c in cs {
                let color = egraph.get_color(*c).unwrap();
                let mut all_ss: IndexSet<_> = known_splits_by_color[&None]
                    .iter()
                    .cloned()
                    .map(|mut s| {
                        s.color = Some(*c);
                        s.update(egraph);
                        s
                    })
                    .collect();
                for p in color.parents() {
                    all_ss.extend(
                        known_splits_by_color[&Some(*p)]
                            .iter()
                            .cloned()
                            .map(|mut s| {
                                s.color = Some(*c);
                                s.update(egraph);
                                s
                            }),
                    );
                }
                known_splits_by_color.insert(Some(*c), all_ss);
            }
        }
        egraph.rebuild();
        for s in splitters {
            let trns = reconstruct_all(egraph, s.color, 4);
            let text = s.by_translation(&trns);
            warn!("  {s} - {}", text);
            #[cfg(feature = "stats")]
            self.stats.known_splits_text.insert(text);
        }
        warn!("Created colors: {:?}", colors);
        // When the API is limited the code is mentally inhibited
        *egraph = self.equiv_reduction(rules, std::mem::take(egraph), run_depth);
        #[cfg(feature = "stats")]
        sample_graph_stats(egraph, StatsReport::CaseSplitDepth(split_depth));
        warn!("Doing Conclusions for depth {split_depth} ----------------");
        for (base, cs) in colors.iter() {
            let split_conclusions = cs
                .iter()
                .map(|c| Self::collect_colored_merged(egraph, &classes, *c))
                .collect_vec();
            Self::merge_conclusions(egraph, base.clone(), &classes, &split_conclusions);
        }
        warn!("Done Conclusions for depth {split_depth} -------------------");
        self.colored_case_split(
            egraph,
            split_depth - 1,
            known_splits_by_color,
            rules,
            run_depth,
        );
        for (base, cs) in colors {
            let split_conclusions = cs
                .iter()
                .map(|c| Self::collect_colored_merged(egraph, &classes, *c))
                .collect_vec();
            Self::merge_conclusions(egraph, base, &classes, &split_conclusions);
        }
    }

    fn keep_splits_case_split(
        &mut self,
        egraph: &mut ThEGraph,
        split_depth: usize,
        known_splits: &IndexSet<Split>,
        rules: &[ThRewrite],
        run_depth: usize,
        vacuity_cases: &mut usize,
    ) {
        if split_depth == 0 {
            return;
        }
        let (splitters, new_known, rected) =
            self.initialize_case_split(known_splits, egraph, split_depth);
        let classes = egraph.classes().map(|c| c.id).collect_vec();

        let mut split_graphs = splitters
            .iter()
            .map(|s| Self::split_graph(egraph, s))
            .collect_vec();
        debug!(
            "Working on following splits in depth {split_depth}:\n{splits}",
            splits=splitters.iter().map(|s| rected
                .get(&s.root)
                .map_or("Bad".to_string(), |x| x.to_string()).to_string() +
                &s.splits
                .iter()
                .map(|r| rected.get(r).map_or("Bad".to_string(), |x| x.to_string()))
                .join(" ")
            ).join(", "),
            split_depth = split_depth
        );
        let conclusions = split_graphs
            .iter_mut()
            .map(|graphs| {
                let sub_concs = graphs
                    .iter_mut()
                    .map(|g| {
                        *g = self.equiv_reduction(rules, std::mem::take(g), run_depth);
                        let res = Self::collect_merged(&g, &classes);
                        res
                    }).collect_vec();
                    sub_concs
            }).collect_vec();
        for split_conclusions in conclusions {
            for gs in split_graphs.iter_mut() {
                for g in gs.iter_mut() {
                    Self::merge_conclusions(g, None, &classes, &split_conclusions);
                }
            }
        }
        for gs in split_graphs.iter_mut() {
            let mut curr_conc = vec![];
            for g in gs.iter_mut() {
                self.keep_splits_case_split(
                    g,
                    split_depth - 1,
                    &new_known,
                    rules,
                    run_depth,
                    vacuity_cases,
                );
                curr_conc.push(Self::collect_merged(g, &classes));
                if g.detect_graph_vacuity() {
                    *vacuity_cases += 1;
                }
            }
            // Merge all conclusions into the original graph
            Self::merge_conclusions(egraph, None, &classes, &curr_conc);
        }
        // Add splits to all_splits - This is only used for keep_splits anyway
        #[cfg(feature = "keep_splits")]
        egraph.all_splits.extend(split_graphs.into_iter().flatten());
    }

    fn inner_case_split(
        &mut self,
        egraph: &mut ThEGraph,
        split_depth: usize,
        known_splits: &IndexSet<Split>,
        rules: &[ThRewrite],
        run_depth: usize,
        vacuity_cases: &mut usize,
    ) {
        if split_depth == 0 {
            return;
        }
        let (splitters, new_known, rected) =
            self.initialize_case_split(known_splits, egraph, split_depth);
        let classes = egraph.classes().map(|c| c.id).collect_vec();

        let mut i = 0;
        for s in splitters {
            let split_conclusions = Self::split_graph(&*egraph, &s)
                .into_iter()
                .map(|g| {
                    debug!(
                        "Working on split {i} of {} -> {:?} in depth {split_depth}",
                        rected
                            .get(&s.root)
                            .map_or("Bad".to_string(), |x| x.to_string()),
                        s.splits
                            .iter()
                            .map(|r| rected.get(r).map_or("Bad".to_string(), |x| x.to_string()))
                            .collect_vec(),
                        i = i,
                        split_depth = split_depth
                    );
                    let mut g = self.equiv_reduction(rules, g, run_depth);
                    self.inner_case_split(
                        &mut g,
                        split_depth - 1,
                        &new_known,
                        rules,
                        run_depth,
                        vacuity_cases,
                    );
                    i += 1;
                    let res = Self::collect_merged(&g, &classes);
                    warn!(
                        "Collected merged {i}: {:?}",
                        res.iter()
                            .grouped(|x| x.1)
                            .iter()
                            .filter(|x| x.1.len() > 1)
                            .collect_vec()
                    );
                    if g.detect_graph_vacuity() {
                        *vacuity_cases += 1;
                    }
                    #[cfg(feature = "keep_splits")]
                    egraph.all_splits.push(g);
                    res
                })
                .collect_vec();
            warn!("Split conclusions: {:?}", split_conclusions);
            Self::merge_conclusions(egraph, None, &classes, &split_conclusions);
        }
    }

    fn initialize_case_split(
        &mut self,
        known_splits: &IndexSet<Split>,
        egraph: &mut EGraph<SymbolLang, ()>,
        split_depth: usize,
    ) -> (Vec<Split>, IndexSet<Split>, IndexMap<Id, Tree>) {
        let known_splits: IndexSet<Split, RandomState> = known_splits
            .iter()
            .map(|e| {
                let mut res = e.clone();
                res.update(egraph);
                res
            })
            .collect();

        let temp = self.find_splitters(egraph);
        let temp_len = temp.len();
        let splitters: Vec<Split> = temp
            .into_iter()
            .filter(|s| !known_splits.contains(s))
            .collect();
        let mut new_known = known_splits.clone();

        new_known.extend(splitters.iter().cloned());
        warn!(
            "Splitters len (temp len: {temp_len}): {} in depth {split_depth}",
            splitters.len()
        );
        let rected = reconstruct_all(egraph, None, 4);
        for s in &splitters {
            let split_text = s.by_translation(&rected);
            warn!("  {} - {}", s, split_text);
            #[cfg(feature = "stats")]
            self.stats.known_splits_text.insert(split_text);
        }
        (splitters, new_known, rected)
    }
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
    use crate::lang::ThEGraph;
    use crate::tests::init_logging;
    use crate::thesy::case_split::CaseSplit;
    use crate::thesy::semantics::Definitions;
    use crate::{TheSy, TheSyConfig};
    use egg::searchers::ToDyn;
    use egg::{EGraph, Language, Pattern, Runner, Searcher, SymbolLang};
    use itertools::Itertools;
    use std::path::PathBuf;
    use std::rc::Rc;

    #[test]
    #[cfg(feature = "split_colored")]
    fn splits_on_ite() {
        let mut config = TheSyConfig::from_path("tests/booleans.th".parse().unwrap());
        let mut case_splitter =
            TheSy::create_case_splitter(config.definitions.case_splitters.clone());
        let mut thesy = TheSy::from(&config);
        thesy.increase_depth();
        thesy.equiv_reduc(&mut config.definitions.rws);
        thesy.increase_depth();
        thesy.equiv_reduc(&mut config.definitions.rws);
        let mut egraph = thesy.egraph;
        let ops = vec![SymbolLang::leaf("true"), SymbolLang::leaf("false")];
        let op_ids = ops.iter().map(|op| op.op_id()).collect_vec();
        egraph.vacuity_ops = vec![op_ids];
        assert!(egraph.detect_color_vacuity().len() == 0);
        case_splitter.case_split(&mut egraph, 1, &config.definitions.rws, 4);
        assert!(egraph.detect_color_vacuity().len() == 0);
        case_splitter.case_split(&mut egraph, 2, &config.definitions.rws, 0);
        assert!(egraph.detect_color_vacuity().len() == 0);
    }

    #[test]
    #[ignore]
    #[cfg(feature = "split_colored")]
    fn no_vacuity_in_and_or() {
        // This test is ignored because case splitting will create vacuity with (= T F) at the moment.
        init_logging();

        let (mut thesy, _rewrites) =
            TheSyConfig::from_path("tests/booleans.th".to_string()).run(None);
        let ops = vec![SymbolLang::leaf("true"), SymbolLang::leaf("false")];
        let op_ids = ops.iter().map(|op| op.op_id()).collect_vec();
        thesy.egraph.vacuity_ops = vec![op_ids];
        assert_eq!(thesy.egraph.detect_color_vacuity().len(), 0);
    }

    #[test]
    fn test_sub_colors_dont_merge_base_assumption() {
        init_logging();

        // Create an EGraph with a and b
        let mut egraph = ThEGraph::default();
        let a = egraph.add_expr(&"a".parse().unwrap());
        let b = egraph.add_expr(&"b".parse().unwrap());
        let c = egraph.add_expr(&"c".parse().unwrap());
        // Create a splitter that splits on a and b.
        // Root applier is "a"
        // cases appliers are "a" and "b"
        // Searcher is "a"
        let root: Pattern<SymbolLang> = ("a").parse().unwrap();
        let cases: Vec<Pattern<SymbolLang>> = vec![("a").parse().unwrap(), ("b").parse().unwrap()];
        let searcher: Rc<dyn Searcher<SymbolLang, ()>> = {
            let p: Pattern<SymbolLang> = ("a").parse().unwrap();
            p.into_rc_dyn()
        };

        let root2: Pattern<SymbolLang> = ("(f a)").parse().unwrap();
        let cases2: Vec<Pattern<SymbolLang>> = vec![("c").parse().unwrap(), ("d").parse().unwrap()];
        let searcher2: Rc<dyn Searcher<SymbolLang, ()>> = {
            let p: Pattern<SymbolLang> = ("(f a)").parse().unwrap();
            p.into_rc_dyn()
        };
        let mut case_splitter =
            TheSy::create_case_splitter(vec![(searcher, root, cases), (searcher2, root2, cases2)]);
        egraph.rebuild();
        let rules = vec![rewrite!("rule"; "b" => "(f b)")];
        case_splitter.case_split(&mut egraph, 2, &rules, 1);
        // hashset of a,b,c ids (after find)
        let mut ids = std::collections::HashSet::new();
        ids.insert(egraph.find(a));
        ids.insert(egraph.find(b));
        ids.insert(egraph.find(c));
        assert_eq!(ids.len(), 3);
    }

    /// Test rewriting on sub_color. Optimally this test would have been in the egg repo, but we
    /// are using TheSy definitions here. We could move it once we know what rewrites are used.
    #[test]
    #[cfg(feature = "split_colored")]
    fn test_rewriting_sub_color() {
        init_logging();

        // load theories/goal1
        let defs = Definitions::from_file(&PathBuf::from("theories/goal1.smt2.th"));
        // Create thesy and case splitter
        let mut splitter = CaseSplit::from_applier_patterns(defs.case_splitters);

        let mut egraph: EGraph<SymbolLang, ()> = EGraph::new(());
        let take_succ_i_exp = "(take i (cons x (cons y nil)))".parse().unwrap();
        let take_succ_i = egraph.add_expr(&take_succ_i_exp);
        let c_base = egraph.create_color();
        // Colored add expression (succ (param_Nat_0 i))
        let i_exp = egraph.add_expr(&"i".parse().unwrap());
        let _nil_exp = egraph.add_expr(&"nil".parse().unwrap());
        let c_succ_i = egraph.colored_add_expr(c_base, &"(succ (param_Nat_0 i))".parse().unwrap());
        egraph.colored_union(c_base, i_exp, c_succ_i);
        egraph.rebuild();
        let mut egraph = Runner::default().with_egraph(egraph).run(&defs.rws).egraph;
        let found = splitter.find_splitters(&mut egraph);
        assert_eq!(
            found.iter().filter(|x| x.color().is_some()).count(),
            1,
            "Found splitters: {:?}",
            found
        );
        let c_sub = egraph.create_sub_color(c_base);
        let param_nat_0_exp = egraph.add_expr(&"(param_Nat_0 i)".parse().unwrap());
        let c_succ_succ_i = egraph.colored_add_expr(
            c_sub,
            &"(succ (param_Nat_0 (param_Nat_0 i)))".parse().unwrap(),
        );
        egraph.colored_union(c_sub, param_nat_0_exp, c_succ_succ_i);
        egraph.rebuild();
        // Remove some of the rws
        println!("RWS: {:?}", defs.rws.len());
        // for i in vec![0, 1, 2, 3, 4, 5, 6, 7, /* 8, 9, */ 10, 11, 12, 13, 14, 15, 16, 17]
        //     .into_iter().rev() {
        //     println!("Removing: {}", defs.rws[i].name());
        //     defs.rws.remove(i);
        // }
        let mut egraph = Runner::default().with_egraph(egraph).run(&defs.rws).egraph;
        egraph.rebuild();
        egraph.colored_dot(c_sub).to_dot("take_drop.dot").unwrap();
        // cons x cons y
        let cons_x_cons_y = egraph.add_expr(&"(cons x (cons y nil))".parse().unwrap());
        assert_eq!(
            egraph.colored_find(c_sub, take_succ_i),
            egraph.colored_find(c_sub, cons_x_cons_y)
        );
    }
}
