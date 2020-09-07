

use egg::{EGraph, SymbolLang, Id, Language};
use std::collections::{HashSet};
use crate::tree::Tree;
use std::iter::FromIterator;
use crate::tools::tools::{combinations, product};
use smallvec::SmallVec;
use multimap::MultiMap;
use std::iter;
use std::rc::Rc;
use std::path::Display;
use smallvec::alloc::fmt::Formatter;
use itertools::Itertools;

struct ETree {
    root: String,
    subtrees: Vec<Rc<ETree>>
}

impl ETree {
    fn leaf(root: String) -> ETree {
        ETree{root, subtrees: Vec::new()}
    }

    fn branch(root: String, subtrees: Vec<Rc<ETree>>) -> ETree {
        ETree{root, subtrees}
    }

    fn to_sexp_string(&self) -> String {
        if self.subtrees.is_empty() {
            self.root.clone()
        } else {
            format!("({} {})", self.root.clone(), self.subtrees.iter().map(|t| t.to_string()).intersperse(" ".parse().unwrap()).collect::<String>())
        }
    }
}

impl std::fmt::Display for ETree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.to_sexp_string())
    }
}

#[derive(Clone)]
struct Entry<'a> {
    edge: &'a SymbolLang,
    eclass: Id,
    children: Vec<&'a Entry<'a>>,
    tree: Rc<ETree>,
}

impl<'a> Entry<'a> {
    fn new(edge: &'a SymbolLang, eclass: Id, children: impl Iterator<Item = &'a Entry<'a>>) -> Entry<'a> {
        let children = Vec::from_iter(children);
        let tree = children.iter().map(|e| e.tree.clone()).collect();
        Entry{edge, eclass, children, tree: Rc::from(ETree::branch(edge.op.to_string(), tree))}
    }
}

pub fn reconstruct_entries(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> MultiMap<Id, Entry> {
    let mut res: MultiMap<Id, Entry> = MultiMap::default();
    let mut available_edges: MultiMap<Id, SymbolLang> = MultiMap::default();
    let mut remaining: Vec<(HashSet<Id>, (Id, SymbolLang))> = Vec::new();
    for c in egraph.classes() {
        for e in c.nodes {
            if e.children.is_empty() {
                available_edges.insert(c.id, e);
            } else {
                remaining.push((HashSet::from_iter(e.children.iter().copied()), (c.id, e)));
            }
        }
    }

    for _ in 0..max_depth {
        let mut new_ids: Vec<&Id> = Vec::new();
        for (id, edges) in available_edges.iter_all() {
            edges.iter().for_each(|edge| {
                if !res.contains_key(&id) {
                    new_ids.push(&id);
                }

                // if there are no children there won't be children combinations
                if edge.is_leaf() {
                    res.insert(*id, Entry::new(edge, *id, iter::empty()));
                }

                let mut combs: Vec<Vec<&Entry>> = product(edge.children.iter()
                                                          .map(|c: &Id| res.get_vec(c).unwrap().clone().iter()));
                for children in combs {
                    res.insert(*id, Entry::new(edge, *id, children.iter().cloned()));
                }
            })
        };
        'outer: for i in 0..remaining.len() {
            for new_id in new_ids.iter() {
                remaining[i].0.remove(new_id);
                if remaining[i].0.is_empty() {
                    available_edges.insert(remaining[i].1 .0, remaining[i].1 .1);
                    remaining.remove(i);
                    continue 'outer;
                }
            }
        }
    }
    return res;
}