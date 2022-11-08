use egg::{Rewrite, SymbolLang, EGraph, Id, Runner, StopReason, Var, Pattern, Searcher, SearchMatches, Applier, Language, Analysis, ColorId};
use itertools::Itertools;
use std::time::Duration;
use std::str::FromStr;
use std::collections::hash_map::RandomState;
use std::rc::Rc;
use std::fmt;
use std::fmt::Debug;
use indexmap::{IndexMap, IndexSet};
use smallvec::alloc::fmt::Formatter;
use egg::reconstruct::{reconstruct, reconstruct_colored};
use egg::appliers::DiffApplier;
use egg::searchers::{FilteringSearcher, ToRc};
use egg::searchers::Matcher;


/// To be used as the op of edges representing potential split
pub const SPLITTER: &'static str = "potential_split";
lazy_static! {
    /// Pattern to find all available splitter edges. Limited arbitrarily to 5 possible splits.
    pub(crate) static ref split_patterns: Vec<Pattern<SymbolLang>> = {
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
    pub fn new(root: Id, splits: Vec<Id>, color: Option<ColorId>) -> Self { Split { root, splits, color } }

    pub(crate) fn update(&mut self, egraph: &EGraph<SymbolLang, ()>) {
        self.root = egraph.opt_colored_find(self.color, self.root);
        for i in 0..self.splits.len() {
            self.splits[i] = egraph.opt_colored_find(self.color, self.splits[i]);
        }
    }

    pub fn create_colors<L: Language, N: Analysis<L>>(&self, egraph: &mut EGraph<L, N>) -> Vec<ColorId> {
        self.splits.iter().map(|id| {
            let c = if let Some(base_color) = self.color {
                egraph.create_sub_color(base_color)
            } else {
                egraph.create_color()
            };
            egraph.colored_union(c, self.root, *id);
            c
        }).collect_vec()
    }
}

impl fmt::Display for Split {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(root: {}, splits [{}], color: {})", self.root, self.splits.iter().map(|x| usize::from(*x).to_string()).intersperse(" ".parse().unwrap()).collect::<String>(), self.color.map(|c| usize::from(c).to_string()).unwrap_or("None".to_string()))
    }
}

pub type SplitApplier = Box<dyn FnMut(&mut EGraph<SymbolLang, ()>, Vec<SearchMatches>) -> Vec<Split>>;

pub struct CaseSplit {
    splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, SplitApplier)>,
    #[cfg(feature = "keep_splits")]
    pub(crate) all_splits: Vec<EGraph<SymbolLang, ()>>,
}

impl Debug for CaseSplit {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "CaseSplit {{ splitter_rules: {:?} }}", self.splitter_rules.iter().map(|(s, _)| (s.to_string(), "TODO print applier")).collect_vec())
    }
}

impl CaseSplit {
    pub fn new(splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>,
                                    SplitApplier)>) -> Self {
        CaseSplit {
            splitter_rules,
            #[cfg(feature = "keep_splits")]
            all_splits: vec![]
        }
    }

    pub fn from_applier_patterns(case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>,
                                                      Pattern<SymbolLang>,
                                                      Vec<Pattern<SymbolLang>>)>) -> CaseSplit {
        let mut res = CaseSplit::new(case_splitters.into_iter()
            .map(|(searcher, pattern, split_evaluators)| {
                let diff_pattern = DiffApplier::new(pattern);
                let applier: SplitApplier = Box::new(move |graph: &mut EGraph<SymbolLang, ()>, sms: Vec<SearchMatches>| {
                    let mut res = vec![];
                    for sm in sms {
                        for subst in &sm.substs {
                            // ECLass is irrelevant
                            let id = diff_pattern.apply_one(graph, sm.eclass, subst);
                            assert_eq!(id.len(), 1);
                            res.push(Split::new(id[0], split_evaluators.iter().map(|ev| ev.apply_one(graph, sm.eclass, &subst)[0]).collect_vec(), subst.color()));
                        }
                    }
                    res
                });
                (searcher.clone(),
                 applier)
            }).collect_vec());
        res
    }

    pub fn extend(&mut self, other: Self) {
        self.splitter_rules.extend(other.splitter_rules)
    }

    // TODO: can this be an iterator?
    fn split_graph(egraph: &EGraph<SymbolLang, ()>,
                   split: &Split) -> Vec<EGraph<SymbolLang, ()>> {
        split.splits.iter().map(|child| {
            let mut new_graph = egraph.clone();
            new_graph.union(split.root, *child);
            new_graph
        }).collect_vec()
    }

    fn equiv_reduction(rules: &[Rewrite<SymbolLang, ()>],
                       egraph: EGraph<SymbolLang, ()>,
                       run_depth: usize) -> EGraph<SymbolLang, ()> {
        let mut runner = Runner::default().with_time_limit(Duration::from_secs(60 * 10)).with_node_limit(egraph.total_number_of_nodes() + 200000).with_egraph(egraph).with_iter_limit(run_depth);
        runner = runner.run(rules);
        match runner.stop_reason.as_ref().unwrap() {
            Saturated => {}
            StopReason::IterationLimit(_) => {}
            StopReason::NodeLimit(_) => { warn!("Stopped case split due to node limit") }
            StopReason::TimeLimit(_) => { warn!("Stopped case split due to time limit") }
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
        runner.egraph
    }

    pub fn find_splitters(&mut self, egraph: &mut EGraph<SymbolLang, ()>) -> Vec<Split> {
        let mut res = vec![];
        for (s, c) in &mut self.splitter_rules {
            res.extend(c(egraph, s.search(egraph)));
            egraph.rebuild();
        }
        res.iter_mut().for_each(|mut x| x.update(egraph));
        info!("Found {} splitters", res.len());
        res.into_iter().unique().collect()
    }

    fn merge_conclusions(egraph: &mut EGraph<SymbolLang, ()>, classes: &Vec<Id>, split_conclusions: Vec<IndexMap<Id, Id>>) {
        let mut group_by_splits: IndexMap<Vec<Id>, IndexSet<Id>> = IndexMap::new();
        for c in classes {
            let key = split_conclusions.iter().map(|m| m[c]).collect_vec();
            group_by_splits.entry(key).or_default().insert(*c);
        }
        for group in group_by_splits.values().filter(|g| g.len() > 1) {
            // print group and reconstruct each member
            debug_assert!(group.iter().filter_map(|id| egraph[*id].color()).unique().count() <= 1);
            // TODO: might need to look into hierarchical colors conclusions.
            let colored = group.into_iter().filter(|id| egraph[**id].color().is_some()).copied().collect_vec();
            let color = colored.first().map(|id| egraph[*id].color().unwrap());
            let black = group.into_iter().filter(|id| egraph[**id].color().is_none()).copied().collect_vec();
            let b_res = black.into_iter().reduce(|a, b| egraph.union(a, b).0);
            let c_res = colored.into_iter().reduce(|a, b| egraph.colored_union(color.clone().unwrap(), a, b).0);
            b_res.map(|id| c_res.map(|id2| egraph.colored_union(color.unwrap(), id, id2)));
        }
        egraph.rebuild();
    }

    fn collect_merged(egraph: &EGraph<SymbolLang, ()>, classes: &Vec<Id>) -> IndexMap<Id, Id> {
        classes.iter().map(|c| (*c, egraph.find(*c))).collect::<IndexMap<Id, Id>>()
    }

    fn collect_colored_merged(egraph: &EGraph<SymbolLang, ()>, classes: &Vec<Id>, color: ColorId) -> IndexMap<Id, Id> {
        classes.iter().map(|eclass| (*eclass, egraph.colored_find(color, *eclass))).collect::<IndexMap<Id, Id>>()
    }

    pub fn case_split(&mut self, egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, rules: &[Rewrite<SymbolLang, ()>], run_depth: usize) {
        if !cfg!(feature = "no_split") {
            if cfg!(feature = "split_clone") {
                self.inner_case_split(egraph, split_depth, &Default::default(), rules, run_depth)
            } else {
                let mut map = IndexMap::default();
                // Hack to not fail first checks
                map.insert(None, Default::default());
                self.colored_case_split(egraph, split_depth, map, rules, run_depth)
            }
        }
    }

    fn colored_case_split(&mut self, egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, mut known_splits_by_color: IndexMap<Option<ColorId>, IndexSet<Split>>, rules: &[Rewrite<SymbolLang, ()>], run_depth: usize) {
        if split_depth == 0 {
            return;
        }

        let color_keys = known_splits_by_color.keys().cloned().collect_vec();
        for color in color_keys {
            let mut splits = known_splits_by_color.remove(&color).unwrap();
            splits = splits.into_iter().map(|mut split| {
                split.update(egraph);
                split
            }).collect();
            known_splits_by_color.insert(color, splits);
        }

        let temp = self.find_splitters(egraph);
        let temp_len = temp.len();
        let mut splitters: Vec<Split> = temp.into_iter()
            .filter(|s| known_splits_by_color.contains_key(&s.color)
                && !known_splits_by_color[&s.color].contains(s))
            .collect();
        warn!("Splitters len (in depth {split_depth}, orig len: {temp_len}): {}", splitters.len());
        warn!("Splittes use colors: {:?}", splitters.iter().map(|s| s.color.as_ref()).counts());
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

        let classes = egraph.classes().map(|c| c.id).collect_vec();
        let colors = splitters.iter().map(|s| s.create_colors(egraph)).collect_vec();
        for cs in &colors {
            for c in cs {
                let color = egraph.get_color(*c).unwrap();
                let mut all_ss: IndexSet<_> = known_splits_by_color[&None].iter().cloned().map(|mut s| {
                    s.color = Some(*c);
                    s.update(egraph);
                    s
                }).collect();
                for p in color.parents() {
                    all_ss.extend(known_splits_by_color[&Some(*p)].iter().cloned().map(|mut s| {
                        s.color = Some(*c);
                        s.update(egraph);
                        s
                    }));
                }
                known_splits_by_color.insert(Some(*c), all_ss);
            }
        }

        egraph.rebuild();
        for s in splitters {
            warn!("  {} - root: {}, cases: {}", s, reconstruct_colored(egraph, s.color, s.root, 2).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string()), s.splits.iter().map(|c| reconstruct(egraph, *c, 3).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string())).intersperse(" ".to_string()).collect::<String>());
        }
        warn!("Created colors: {:?}", colors);
        // When the API is limited the code is mentally inhibited
        egraph.dot().to_dot(format!("before_colored_case_split_{}.dot", egraph.colors().count())).unwrap();
        *egraph = Self::equiv_reduction(rules, std::mem::take(egraph), run_depth);
        self.colored_case_split(egraph, split_depth - 1, known_splits_by_color, rules, run_depth);
        colors.iter().for_each(|cs| cs.iter()
            .for_each(|c|
                egraph.colored_dot(*c)
                    .to_dot(format!("after_case_split_color_{}.dot", c)).unwrap()));
        let pattern_results = Pattern::from_str("(= ?x ?y)").unwrap().search(egraph);
        warn!("Results for (= ?x ?y) : {:?}", pattern_results);
        let filtering_searcher = FilteringSearcher::searcher_is_true(Pattern::from_str("(= ?x ?y)").unwrap());
        let matcher = crate::searchers::PatternMatcher::new("true".parse().unwrap());
        warn!("Matcher results are: {:?}", matcher.match_(egraph, &pattern_results[0].substs[0]));
        warn!("Results for (= ?x ?y) == true : {:?}", filtering_searcher.search(egraph));
        for cs in colors {
            let split_conclusions = cs.iter()
                .map(|c| {
                    Self::collect_colored_merged(egraph, &classes, *c)
                })
                .collect_vec();
            Self::merge_conclusions(egraph, &classes, split_conclusions);
        }
    }

    fn inner_case_split(&mut self, egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, known_splits: &IndexSet<Split>, rules: &[Rewrite<SymbolLang, ()>], run_depth: usize) {
        if split_depth == 0 {
            return;
        }
        let known_splits: IndexSet<Split, RandomState> = known_splits.iter().map(|e| {
            let mut res = e.clone();
            res.update(egraph);
            res
        }).collect();

        let temp = self.find_splitters(egraph);
        let temp_len = temp.len();
        let splitters: Vec<&Split> = temp.iter()
            .filter(|s| !known_splits.contains(*s))
            .collect();
        let mut new_known = known_splits.clone();

        new_known.extend(splitters.iter().cloned().cloned());
        // if !splitters.is_empty() {
            warn!("Splitters len (temp len: {temp_len}): {}", splitters.len());
            for s in &splitters {
                warn!("  {} - root: {}, cases: {}", s, reconstruct(egraph, s.root, 3).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string()), s.splits.iter().map(|c| reconstruct(egraph, *c, 3).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string())).intersperse(" ".to_string()).collect::<String>());
            }
        // }

        let classes = egraph.classes().map(|c| c.id).collect_vec();

        let mut i = 0;
        for s in splitters {
            let split_conclusions = Self::split_graph(&*egraph, s).into_iter().map(|g| {
                g.dot().to_dot(format!("before_case_split_{}.dot", i)).unwrap();
                let mut g = Self::equiv_reduction(rules, g, run_depth);
                self.inner_case_split(&mut g, split_depth - 1, &new_known, rules, run_depth);
                g.dot().to_dot(format!("after_case_split_{}.dot", i)).unwrap();
                i += 1;
                let res = Self::collect_merged(&g, &classes);
                warn!("Collected merged {i}: {:?}", res);
                #[cfg(feature = "keep_splits")]
                self.all_splits.push(g);
                res
            }).collect_vec();
            warn!("Split conclusions: {:?}", split_conclusions);
            Self::merge_conclusions(egraph, &classes, split_conclusions);
        }
    }
}

#[cfg(test)]
mod tests {
    use egg::{Pattern, RecExpr, SymbolLang};
    use crate::{TheSy, TheSyConfig, Language, tests};
    use itertools::Itertools;
    use crate::tests::ProofMode;

    #[test]
    #[cfg(feature = "split_colored")]
    fn splits_on_ite() {
        let mut config = TheSyConfig::from_path("tests/booleans.th".parse().unwrap());
        let mut case_splitter = TheSy::create_case_splitter(config.definitions.case_splitters.clone());
        let mut thesy = TheSy::from(&config);
        thesy.increase_depth();
        thesy.equiv_reduc(&mut config.definitions.rws);
        thesy.increase_depth();
        thesy.equiv_reduc(&mut config.definitions.rws);
        let mut egraph = thesy.egraph;
        let ops = vec![SymbolLang::leaf("true"), SymbolLang::leaf("false")];
        let op_ids = ops.iter().map(|op| op.op_id()).collect_vec();
        assert!(egraph.detect_vacuity(&op_ids).len() == 0);
        case_splitter.case_split(&mut egraph, 1, &config.definitions.rws, 4);
        assert!(egraph.detect_vacuity(&op_ids).len() == 0);
        case_splitter.case_split(&mut egraph, 2, &config.definitions.rws, 0);
        assert!(egraph.detect_vacuity(&op_ids).len() == 0);
    }

    #[test]
    #[cfg(feature = "split_colored")]
    fn no_vacuity_in_and_or() {
        let (thesy, rewrites) = TheSyConfig::from_path("tests/booleans.th".to_string()).run(None);
        let ops = vec![SymbolLang::leaf("true"), SymbolLang::leaf("false")];
        let op_ids = ops.iter().map(|op| op.op_id()).collect_vec();
        assert!(thesy.egraph.detect_vacuity(&op_ids).len() == 0);
    }
}