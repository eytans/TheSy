use egg::{EGraph, SymbolLang, Id, Language};
use std::collections::{HashMap, HashSet};
use crate::tree::Tree;
use std::iter::FromIterator;
use crate::tools::tools::combinations;

pub mod multisearcher;
pub mod appliers;

pub fn reconstruct_all(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> HashMap<Id, HashSet<Tree>> {
    let mut res: HashMap<Id, HashSet<Tree>> = HashMap::default();
    for _ in 0..max_depth {
        let keys: HashSet<Id> = HashSet::from_iter(res.keys().map(|id| id.clone()));
        // Collecting all edges from graph that can be translated
        let equiv_classes = egraph.classes()
            .map(|c| (c.id, c.nodes.iter()
                .filter(|n| n.children.iter()
                    .all(|child| keys.contains(child)))
            ));
        for (id, edges) in equiv_classes {
            edges.for_each(|edge| {
                if !res.contains_key(&id) {
                    res.insert(id.clone(), HashSet::default());
                }
                if edge.is_leaf() {
                    res.get_mut(&id).unwrap().insert(Tree::leaf(edge.op.to_string()));
                }

                // Why cant I borrow a hashset and then added a different hashset to res?
                // If res would hold refs it wouldn't be so bad but then where are trees held?
                let dup_sets =
                    edge.children.iter().map(|c: &Id| res.get(c).unwrap())
                        .map(|hs| HashSet::from_iter(hs.iter().map(|t| t.clone())))
                        .collect::<Vec<HashSet<Tree>>>();
                let combs = combinations(&Vec::from_iter(dup_sets.iter()));
                for children in combs {
                    let mut updated_children = Vec::new();
                    for c in children {
                        updated_children.push(c.clone());
                    }
                    let new_tree = Tree::branch(edge.op.to_string(),
                                                updated_children);
                    res.get_mut(&id).unwrap().insert(new_tree);
                }
            })
        };
    }
    return res;
}