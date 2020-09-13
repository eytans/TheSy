use egg::{EGraph, SymbolLang, Id, Language};
use std::collections::{HashMap, HashSet};
use crate::tree::Tree;
use crate::tools::tools::{combinations};
use std::rc::Rc;
use std::time::SystemTime;
use itertools::{Itertools};
use std::iter;


pub fn reconstruct_all(graph: &EGraph<SymbolLang, ()>, max_depth: usize) -> HashMap<Id, HashSet<Rc<Tree>>> {
    for c in graph.classes() {
        let set = c.nodes.iter().collect::<HashSet<&SymbolLang>>();
        for c1 in graph.classes() {
            for n in c1.nodes.iter() {
                assert!(!set.contains(n) || c.id == c1.id)
            }
        }
    }
    let edges = graph.classes().filter(|c| graph.find(c.id) == c.id).flat_map(|c| iter::once(c.id).cycle().zip(c.nodes.iter())).collect_vec();
    // let idToType = inputEdges.filter(_.edgeType.identifier == Language.typeId).map(e => (e.sources(0), Programs.reconstruct(inputEdges, e.sources(1)).head)).toMap
    let mut known_terms: HashMap<Id, HashSet<Rc<Tree>>> = HashMap::new();
    let mut last_level: HashSet<(Id, Rc<Tree>)> = edges.iter().filter_map(|(id, e)| {
        if e.is_leaf() {
            let tree = Rc::new(Tree::leaf(e.op.to_string()));
            if !known_terms.contains_key(id) {
                known_terms.insert(*id, HashSet::new());
            }
            known_terms.get_mut(id).unwrap().insert(tree.clone());
            Some((*id, tree))
        } else {
            None
        }
    }).collect();
    let mut levels = vec![last_level];

    // id to edges that might be available
    // let edges_by_reqiurments = collection.mutable.HashMultiMap.empty[HyperTermId, (Int, HyperEdge[HyperTermId, HyperTermIdentifier])]
    let mut edges_by_reqiurments = HashMap::new();
    for x in edges.iter() {
        for (i, s) in x.1.children.iter().enumerate() {
            assert_eq!(graph.find(*s), *s);
            if !edges_by_reqiurments.contains_key(s) {
                edges_by_reqiurments.insert(*s, HashSet::new());
            }
            edges_by_reqiurments.get_mut(s).unwrap().insert((i, *x));
        }
    };

    // The reconstruct itself.
    for d in 0..max_depth {
        println!("depth {}", d);
        last_level = HashSet::new();
        for e in levels.last().unwrap() {
            for v in edges_by_reqiurments.get(&e.0) {
                for (i_to_fill, e_to_fill) in v {
                    let params_to_fill = e_to_fill.1.children.iter().take(*i_to_fill).chain(&e_to_fill.1.children[i_to_fill + 1..]);
                    let trees = params_to_fill.filter_map(|h_id| known_terms.get(h_id).map_or(None, |x| Some(x.iter().cloned()))).collect_vec();
                    if trees.len() == e_to_fill.1.children.len() - 1 {
                        for mut fillers in combinations(trees.into_iter()) {
                            fillers.insert(*i_to_fill, e.1.clone());
                            last_level.insert((e.0, Rc::new(Tree::branch(e_to_fill.1.op.to_string(), fillers))));
                        }
                    }
                }
            }
        }

        for e in last_level.clone() {
            if !known_terms.contains_key(&e.0) {
                known_terms.insert(e.0, HashSet::new());
            }
            known_terms.get_mut(&e.0).unwrap().insert(e.1);
        }

        levels.push(last_level);
    }

    known_terms
    // known_terms.into_iter().flat_map(|x| iter::once(x.0).cycle().zip(x.1.into_iter())).collect::<HashSet<(Id, Rc<Tree>)>>()
}
