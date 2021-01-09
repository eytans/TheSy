use egg::{Rewrite, SymbolLang, EGraph, Id, Runner, StopReason, EClass, Var, Pattern, Searcher, SearchMatches, Applier};
use itertools::Itertools;
use std::time::Duration;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;
use std::collections::hash_map::RandomState;
use std::rc::Rc;
use std::path::Display;
use std::fmt;
use smallvec::alloc::fmt::Formatter;

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
}

impl Split {
    pub fn new(root: Id, splits: Vec<Id>) -> Self {Split{root, splits}}

    pub(crate) fn update(&mut self, egraph: &EGraph<SymbolLang, ()>) {
        self.root = egraph.find(self.root);
        for i in 0..self.splits.len() {
            self.splits[i] = egraph.find(self.splits[i]);
        }
    }
}

impl fmt::Display for Split {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(root: {}, splits [{}])", self.root, self.splits.iter().map(|x| usize::from(*x).to_string()).intersperse(" ".parse().unwrap()).collect::<String>())
    }
}

pub type SplitApplier = Box<dyn FnMut(&mut EGraph<SymbolLang, ()>, Vec<SearchMatches>) -> Vec<Split>>;

pub struct CaseSplit {
    splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, SplitApplier)>,
}

impl CaseSplit {
    pub fn new(splitter_rules: Vec<(Rc<dyn Searcher<SymbolLang, ()>>,
                                    SplitApplier)>) -> Self {
        CaseSplit { splitter_rules }
    }

    pub fn from_applier_patterns(case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Var, Vec<Pattern<SymbolLang>>)>) -> CaseSplit {
        let mut res = CaseSplit::new(case_splitters.into_iter().map(|(searcher, root, split_evaluators)| {
            let applier: SplitApplier = Box::new(move |graph: &mut EGraph<SymbolLang, ()>, sms: Vec<SearchMatches>| {
                let mut res = vec![];
                for sm in sms {
                    for subst in &sm.substs {
                        res.push(Split::new(subst[root], split_evaluators.iter().map(|ev| ev.apply_one(graph, sm.eclass, &subst)[0]).collect_vec()));
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
        runner.egraph.rebuild();
        runner.egraph
    }

    pub fn find_splitters(&mut self, egraph: &mut EGraph<SymbolLang, ()>) -> Vec<Split> {
        let mut res = vec![];
        for (s, c) in &mut self.splitter_rules {
            res.extend(c(egraph, s.search(egraph)));
        }
        res.into_iter().unique().collect_vec()
    }

    fn merge_conclusions(egraph: &mut EGraph<SymbolLang, ()>, classes: &Vec<Id>, split_conclusions: Vec<HashMap<Id, Id>>) {
        let mut group_by_splits: HashMap<Vec<Id>, HashSet<Id>> = HashMap::new();
        for c in classes {
            let key = split_conclusions.iter().map(|m| m[c]).collect_vec();
            if !group_by_splits.contains_key(&key) {
                group_by_splits.insert(key.clone(), HashSet::new());
            }
            group_by_splits.get_mut(&key).unwrap().insert(*c);
        }
        for group in group_by_splits.values().filter(|g| g.len() > 1) {
            let first = group.iter().next().unwrap();
            for id in group.iter().dropping(1) {
                egraph.union(*first, *id);
            }
        }
        egraph.rebuild();
    }
    fn collect_merged(egraph: &EGraph<SymbolLang, ()>, classes: &Vec<Id>) -> HashMap<Id, Id> {
        classes.iter().map(|c| (*c, egraph.find(*c))).collect::<HashMap<Id, Id>>()
    }

    pub fn case_split(&mut self, egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, rules: &[Rewrite<SymbolLang, ()>], run_depth: usize) {
        if !cfg!(feature = "no_split") {
            self.inner_case_split(egraph, split_depth, &Default::default(), rules, run_depth)
        }
    }

    fn inner_case_split(&mut self, egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, known_splits: &HashSet<Split>, rules: &[Rewrite<SymbolLang, ()>], run_depth: usize) {
        if split_depth == 0 {
            return;
        }

        let known_splits: HashSet<Split, RandomState> = known_splits.iter().map(|e| {
                    let mut res = e.clone();
                    res.update(egraph);
                    res
                }).collect();

                let temp = self.find_splitters(egraph);
                let splitters: Vec<&Split> = temp.iter()
                    // .filter(|s| !known_splits.contains(s))
                    .collect();
                let mut new_known = known_splits.clone();
                new_known.extend(splitters.iter().cloned().cloned());

                let classes = egraph.classes().map(|c| c.id).collect_vec();

                for s in splitters {
                    let split_conclusions = Self::split_graph(&*egraph, s).into_iter().map(|g| {
                        let mut g = Self::equiv_reduction(rules, g, run_depth);
                self.inner_case_split(&mut g, split_depth - 1, &new_known, rules, run_depth);
                Self::collect_merged(&g, &classes)
            }).collect_vec();
            Self::merge_conclusions(egraph, &classes, split_conclusions);
        }
    }
}
