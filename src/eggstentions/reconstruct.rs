use egg::{EGraph, SymbolLang, Id, Language};
use std::collections::{HashMap, HashSet};
use crate::tree::Tree;
use std::iter::FromIterator;
use crate::tools::tools::combinations;
use std::rc::Rc;
use std::alloc::System;
use std::time::SystemTime;

pub fn reconstruct_all(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> HashMap<Id, HashSet<Rc<Tree>>> {
    let mut res: HashMap<Id, HashSet<Rc<Tree>>> = HashMap::default();
    for _ in 0..max_depth {
        let keys: HashSet<Id> = HashSet::from_iter(res.keys().copied());
        // Collecting all edges from graph that can be translated
        let equiv_classes = egraph.classes()
            .map(|c| (c.id, c.nodes.iter()
                .filter(|n| n.children.iter()
                    .all(|child| keys.contains(child)))
            ));
        for (id, edges) in equiv_classes {
            edges.for_each(|edge| {
                if !res.contains_key(&id) {
                    res.insert(id, HashSet::with_capacity(1000000));
                }

                if edge.is_leaf() {
                    res.get_mut(&id).unwrap().insert(Rc::new(Tree::leaf(edge.op.to_string())));
                }

                let dup_sets =
                    edge.children.iter().map(|c: &Id| res.get(c).unwrap())
                        .map(|hs| HashSet::from_iter(hs.iter().map(|t| t.clone())))
                        .collect::<Vec<HashSet<Rc<Tree>>>>();

                let start =  SystemTime::now();
                let combs = combinations(&Vec::from_iter(dup_sets.iter()));
                println!("done: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
                for children in combs {
                    let new_tree = Rc::new(Tree::branch(edge.op.to_string(),
                                                        children));
                    res.get_mut(&id).unwrap().insert(new_tree);
                }
                println!("inserted: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
            })
        };
    }
    return res;
}
