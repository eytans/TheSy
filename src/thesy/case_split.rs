use egg::{Rewrite, SymbolLang, EGraph, Id, Runner, StopReason, Var, Pattern, Searcher, SearchMatches, Applier, Language, Analysis, ColorId};
use itertools::Itertools;
use std::time::Duration;
use std::collections::hash_map::RandomState;
use std::rc::Rc;
use std::fmt;
use std::fmt::Debug;
use indexmap::{IndexMap, IndexSet};
use smallvec::alloc::fmt::Formatter;
use egg::reconstruct::{reconstruct, reconstruct_all};
use egg::appliers::DiffApplier;
use egg::searchers::{FilteringSearcher, ToRc};
use crate::egg::tools::tools::Grouped;

use std::str::FromStr;
use crate::lang::{ThEGraph, ThRewrite};


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

    pub fn color(&self) -> Option<ColorId> { self.color }

    pub(crate) fn update(&mut self, egraph: &ThEGraph) {
        self.root = egraph.opt_colored_find(self.color, self.root);
        for i in 0..self.splits.len() {
            self.splits[i] = egraph.opt_colored_find(self.color, self.splits[i]);
        }
    }

    pub fn create_colors<L: Language, N: Analysis<L>>(&self, egraph: &mut EGraph<L, N>) -> Vec<ColorId> {
        egraph.rebuild();
        self.splits.iter().map(|id| {
            let c = if let Some(base_color) = self.color {
                egraph.create_sub_color(base_color)
            } else {
                egraph.create_color()
            };
            let fixer = |id: Id| egraph.get_color(c).unwrap().translate_from_base(id);
            egraph.colored_union(c, fixer(self.root), fixer(*id));
            egraph.rebuild();
            c
        }).collect_vec()
    }
}

impl fmt::Display for Split {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(root: {}, splits [{}], color: {})", self.root, self.splits.iter().map(|x| usize::from(*x).to_string()).intersperse(" ".parse().unwrap()).collect::<String>(), self.color.map(|c| usize::from(c).to_string()).unwrap_or("None".to_string()))
    }
}

pub type SplitApplier = Box<dyn FnMut(&mut ThEGraph, Vec<SearchMatches>) -> Vec<Split>>;

pub struct CaseSplit {
    splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, SplitApplier)>,
    #[cfg(feature = "keep_splits")]
    pub(crate) all_splits: Vec<ThEGraph>,
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
                let applier: SplitApplier = Box::new(move |graph: &mut ThEGraph, sms: Vec<SearchMatches>| {
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
    fn split_graph(egraph: &ThEGraph,
                   split: &Split) -> Vec<ThEGraph> {
        split.splits.iter().map(|child| {
            let mut new_graph = egraph.clone();
            new_graph.union(split.root, *child);
            new_graph
        }).collect_vec()
    }

    fn equiv_reduction(rules: &[ThRewrite],
                       egraph: ThEGraph,
                       run_depth: usize) -> ThEGraph {
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

    pub fn find_splitters(&mut self, egraph: &mut ThEGraph) -> Vec<Split> {
        debug!("Finding splitters");
        let mut res = vec![];
        for (s, c) in &mut self.splitter_rules {
            res.extend(c(egraph, s.search(egraph)));
            egraph.rebuild();
        }
        res.iter_mut().for_each(|mut x| x.update(egraph));
        debug!("Found {} splitters", res.len());
        res.into_iter().unique().collect()
    }

    fn merge_conclusions(egraph: &mut ThEGraph, color: Option<ColorId>, classes: &Vec<Id>, split_conclusions: Vec<IndexMap<Id, Id>>) {
        let mut group_by_splits: IndexMap<Vec<Id>, IndexSet<Id>> = IndexMap::new();
        for c in classes {
            let key = split_conclusions.iter().map(|m| m[c]).collect_vec();
            group_by_splits.entry(key).or_default().insert(*c);
        }
        for group in group_by_splits.values().filter(|g| g.len() > 1) {
            // print group and reconstruct each member
            debug_assert!(group.iter().filter_map(|id| egraph[*id].color()).unique().count() <= 1);
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
        classes.iter().map(|c| (*c, egraph.find(*c))).collect::<IndexMap<Id, Id>>()
    }

    fn collect_colored_merged(egraph: &ThEGraph, classes: &Vec<Id>, color: ColorId) -> IndexMap<Id, Id> {
        classes.iter().map(|eclass| {
            let fixed = egraph.get_color(color).unwrap()
                .translate_to_base(egraph.colored_find(color, *eclass));
            (*eclass, fixed)
        }).collect::<IndexMap<Id, Id>>()
    }

    pub fn case_split(&mut self, egraph: &mut ThEGraph, split_depth: usize, rules: &[ThRewrite], run_depth: usize) {
        if !cfg!(feature = "no_split") {
            info!("Case splitting with depth {}", split_depth);
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

    fn colored_case_split(&mut self, egraph: &mut ThEGraph, split_depth: usize, mut known_splits_by_color: IndexMap<Option<ColorId>, IndexSet<Split>>, rules: &[ThRewrite], run_depth: usize) {
        if split_depth == 0 {
            return;
        }
        debug!("Colored Case splitting with depth {}", split_depth);
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
        for s in &temp {
            let trns = reconstruct_all(egraph, s.color, 4);
            debug!("  {} - root: {}, cases: {}", s, trns.get(&s.root).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string()), s.splits.iter().map(|c| trns.get(c).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string())).intersperse(" ".to_string()).collect::<String>());
        }
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

        egraph.rebuild();
        let classes = egraph.classes().map(|c| c.id).collect_vec();
        let colors = splitters.iter().map(|s| (s.color.clone(), s.create_colors(egraph))).collect_vec();
        for (_, cs) in &colors {
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
            let trns = reconstruct_all(egraph, s.color, 4);
            warn!("  {} - root: {}, cases: {}", s, trns.get(&s.root).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string()), s.splits.iter().map(|c| trns.get(c).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string())).intersperse(" ".to_string()).collect::<String>());
        }
        warn!("Created colors: {:?}", colors);
        // When the API is limited the code is mentally inhibited
        *egraph = Self::equiv_reduction(rules, std::mem::take(egraph), run_depth);
        self.colored_case_split(egraph, split_depth - 1, known_splits_by_color, rules, run_depth);
        warn!("Doing Conclusions for depth {split_depth} ----------------");
        for (base, cs) in colors {
            let split_conclusions = cs.iter()
                .map(|c| {
                    Self::collect_colored_merged(egraph, &classes, *c)
                })
                .collect_vec();
            Self::merge_conclusions(egraph, base, &classes, split_conclusions);
        }
        warn!("Done Conclusions for depth {split_depth} -------------------");
    }

    fn inner_case_split(&mut self, egraph: &mut ThEGraph, split_depth: usize, known_splits: &IndexSet<Split>, rules: &[ThRewrite], run_depth: usize) {
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
        warn!("Splitters len (temp len: {temp_len}): {} in depth {split_depth}", splitters.len());
        let rected = reconstruct_all(egraph, None, 4);
        for s in &splitters {
            let root_text = rected.get(&s.root).map(|x| x.to_string()).unwrap_or("No reconstruct".to_string());
            let cases_text = s.splits.iter()
                .map(|c| rected.get(c).map(|x| x.to_string())
                    .unwrap_or("No reconstruct".to_string()))
                .intersperse(" ".to_string()).collect::<String>();
            warn!("  {} - root: {}, cases: {}", s, root_text, cases_text);
        }

        let classes = egraph.classes().map(|c| c.id).collect_vec();

        let mut i = 0;
        for s in splitters {
            let split_conclusions = Self::split_graph(&*egraph, s).into_iter().map(|g| {
                debug!("Working on split {i} of {} -> {:?} in depth {split_depth}",
                    rected.get(&s.root).map_or("Bad".to_string(), |x| x.to_string()),
                    s.splits.iter().map(|r| rected.get(r).map_or("Bad".to_string(), |x| x.to_string())).collect_vec(),
                    i = i, split_depth = split_depth);
                let mut g = Self::equiv_reduction(rules, g, run_depth);
                self.inner_case_split(&mut g, split_depth - 1, &new_known, rules, run_depth);
                i += 1;
                let res = Self::collect_merged(&g, &classes);
                warn!("Collected merged {i}: {:?}", res.iter().grouped(|x| x.1).iter().filter(|x| x.1.len() > 1).collect_vec());
                #[cfg(feature = "keep_splits")]
                self.all_splits.push(g);
                res
            }).collect_vec();
            warn!("Split conclusions: {:?}", split_conclusions);
            Self::merge_conclusions(egraph, None, &classes, split_conclusions);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::rc::Rc;
    use egg::{ColorId, EGraph, Id, Pattern, RecExpr, Runner, Searcher, SymbolLang};
    use egg::searchers::ToDyn;
    use crate::{TheSy, TheSyConfig, Language, tests};
    use itertools::Itertools;
    use crate::lang::ThEGraph;
    use crate::tests::{init_logging, ProofMode};
    use crate::thesy::case_split::CaseSplit;
    use crate::thesy::semantics::Definitions;

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
    #[ignore]
    #[cfg(feature = "split_colored")]
    fn no_vacuity_in_and_or() {
        // This test is ignored because case splitting will create vacuity with (= T F) at the moment.
        init_logging();

        let (thesy, rewrites) = TheSyConfig::from_path("tests/booleans.th".to_string()).run(None);
        let ops = vec![SymbolLang::leaf("true"), SymbolLang::leaf("false")];
        let op_ids = ops.iter().map(|op| op.op_id()).collect_vec();
        assert_eq!(thesy.egraph.detect_vacuity(&op_ids).len(), 0);
    }

    #[test]
    #[cfg(feature = "split_colored")]
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
        let mut case_splitter = TheSy::create_case_splitter(vec![
            (searcher, root, cases),
            (searcher2, root2, cases2)
        ]);
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
        let mut defs = Definitions::from_file(&PathBuf::from("theories/goal1.smt2.th"));
        // Create thesy and case splitter
        let mut splitter = CaseSplit::from_applier_patterns(defs.case_splitters);

        let mut egraph: EGraph<SymbolLang, ()> = EGraph::new(());
        let take_succ_i_exp = "(take i (cons x (cons y nil)))".parse().unwrap();
        let take_succ_i = egraph.add_expr(&take_succ_i_exp);
        let c_base = egraph.create_color();
        // Colored add expression (succ (param_Nat_0 i))
        let i_exp = egraph.add_expr(&"i".parse().unwrap());
        let nil_exp = egraph.add_expr(&"nil".parse().unwrap());
        let c_succ_i = egraph.colored_add_expr(c_base, &"(succ (param_Nat_0 i))".parse().unwrap());
        egraph.colored_union(c_base, i_exp, c_succ_i);
        egraph.rebuild();
        let mut egraph = Runner::default().with_egraph(egraph).run(&defs.rws).egraph;
        let found = splitter.find_splitters(&mut egraph);
        assert_eq!(found.iter().filter(|x| x.color().is_some()).count(), 1, "Found splitters: {:?}", found);
        let c_sub = egraph.create_sub_color(c_base);
        let param_nat_0_exp = egraph.add_expr(&"(param_Nat_0 i)".parse().unwrap());
        let c_succ_succ_i = egraph.colored_add_expr(c_sub, &"(succ (param_Nat_0 (param_Nat_0 i)))".parse().unwrap());
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
        egraph.colored_dot(c_sub).to_dot("take_drop.dot");
        assert_eq!(egraph.colored_find(c_sub, take_succ_i), egraph.colored_find(c_sub, nil_exp));
    }
}