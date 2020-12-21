use egg::{Rewrite, SymbolLang, EGraph, Id, Runner, StopReason, EClass, Var, Pattern, Searcher};
use itertools::Itertools;
use std::time::Duration;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

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

/// Case splitting works by cloning the graph and merging the different possibilities.
/// Enabling recursivly splitting all
fn case_split(rules: &[Rewrite<SymbolLang, ()>], egraph: &mut EGraph<SymbolLang, ()>, root: Id, splits: Vec<Id>, split_depth: usize, run_depth: usize, dont_use: &HashSet<(Id, Vec<Id>)>) {
    let classes = egraph.classes().collect_vec();
    // TODO: parallel
    let after_splits = splits.iter().map(|child| {
        let mut new_graph = egraph.clone();
        new_graph.union(root, *child);
        // TODO: graph limit enhancing runner, with rules sorting
        let mut runner = Runner::default().with_time_limit(Duration::from_secs(60 * 10)).with_node_limit(new_graph.total_number_of_nodes() + 50000).with_egraph(new_graph).with_iter_limit(run_depth);
        runner = runner.run(rules );
        match runner.stop_reason.as_ref().unwrap() {
            Saturated => {}
            StopReason::IterationLimit(_) => {}
            StopReason::NodeLimit(_) => { warn!("Stopped case split due to node limit") }
            StopReason::TimeLimit(_) => { warn!("Stopped case split due to time limit") }
            StopReason::Other(_) => {}
        };
        runner.egraph.rebuild();
        _case_split_all(rules, &mut runner.egraph, split_depth - 1, run_depth, dont_use);
        classes.iter().map(|c| (c.id, runner.egraph.find(c.id))).collect::<HashMap<Id, Id>>()
    }).collect_vec();
    let mut group_by_splits: HashMap<Vec<Id>, HashSet<Id>> = HashMap::new();
    for c in classes {
        let key = after_splits.iter().map(|m| m[&c.id]).collect_vec();
        if !group_by_splits.contains_key(&key) {
            group_by_splits.insert(key.clone(), HashSet::new());
        }
        group_by_splits.get_mut(&key).unwrap().insert(c.id);
    }
    for group in group_by_splits.values().filter(|g| g.len() > 1) {
        let first = group.iter().next().unwrap();
        for id in group.iter().dropping(1) {
            egraph.union(*first, *id);
        }
    }
    egraph.rebuild();
}

pub fn case_split_all(rules: &[Rewrite<SymbolLang, ()>],
                      egraph: &mut EGraph<SymbolLang, ()>,
                      split_depth: usize, run_depth: usize) {
    _case_split_all(rules, egraph, split_depth, run_depth, &HashSet::new())
}

fn _case_split_all(rules: &[Rewrite<SymbolLang, ()>],
                   egraph: &mut EGraph<SymbolLang, ()>,
                   split_depth: usize, run_depth: usize,
                   dont_use: &HashSet<(Id, Vec<Id>)>) {
    if split_depth == 0 {
        return;
    }
    let new_dont_use = dont_use.iter()
        .map(|(root, children)|
            (
                egraph.find(*root),
                children.iter().map(|c| egraph.find(*c)).collect_vec()
            )
        ).collect::<HashSet<(Id, Vec<Id>)>>();
    let root_var: Var = "?root".parse().unwrap();
    let children_vars: Vec<Var> = (0..5).map(|i| format!("?c{}", i).parse().unwrap()).collect_vec();
    let mut splitters: Vec<(Id, Vec<Id>)> = split_patterns.iter().enumerate()
        .flat_map(|(i, p)| {
            let results = p.search(egraph).into_iter().flat_map(|x| x.substs);
            results.map(|s| (
                *s.get(root_var).unwrap(), // Root
                (0..i + 2).map(|i| *s.get(children_vars[i]).unwrap()).collect_vec() // Params
            )).filter(|x| !new_dont_use.contains(x))
                .collect_vec()
        })
        .collect_vec();
    if splitters.is_empty() {
        return;
    }
    let classes: HashMap<Id, &EClass<SymbolLang, ()>> = egraph.classes().map(|c| (c.id, c)).collect();
    let mut needed: HashSet<Id> = splitters.iter().map(|x| x.0).collect();
    let mut translatable = HashSet::new();
    for _ in 0..=split_depth {
        'outer: for id in needed.clone() {
            let c = classes[&id];
            if translatable.contains(&c.id) {
                continue;
            }
            for edge in c.nodes.iter() {
                if edge.children.iter().all(|child| translatable.contains(child)) {
                    translatable.insert(c.id);
                    needed.remove(&c.id);
                    continue 'outer;
                } else {
                    needed.extend(edge.children.iter().filter(|child| !translatable.contains(child)));
                }
            }
        }
    }
    warn!("# of splitters: {}", splitters.len());
    splitters.iter().filter(|s| translatable.contains(&s.0)).enumerate().for_each(|(i, (root, params))| {
        let mut updated_dont_use = new_dont_use.clone();
        updated_dont_use.extend(splitters.iter().take(i + 1).cloned());
        case_split(rules, egraph, *root, params.clone(), split_depth, run_depth, &updated_dont_use);
    });
}
