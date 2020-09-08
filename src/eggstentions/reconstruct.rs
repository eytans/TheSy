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

pub struct ETree {
    root: String,
    subtrees: Vec<Rc<ETree>>,
}

impl ETree {
    fn leaf(root: String) -> ETree {
        ETree { root, subtrees: Vec::new() }
    }

    fn branch(root: String, subtrees: Vec<Rc<ETree>>) -> ETree {
        ETree { root, subtrees }
    }

    pub fn to_sexp_string(&self) -> String {
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
pub struct Entry<'a> {
    edge: &'a SymbolLang,
    eclass: Id,
    children: Vec<Rc<Entry<'a>>>,
    pub(crate) tree: Rc<ETree>,
}

impl<'a> Entry<'a> {
    fn new(edge: &'a SymbolLang, eclass: Id, children: impl Iterator<Item=Rc<Entry<'a>>>) -> Entry<'a> {
        let children = Vec::from_iter(children);
        let tree = children.iter().map(|e| e.tree.clone()).collect();
        Entry { edge, eclass, children, tree: Rc::from(ETree::branch(edge.op.to_string(), tree)) }
    }
}

// Dynamic programming method of creating all trees in the graph.
pub fn reconstruct_entries(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> MultiMap<Id, Rc<Entry>> {
    // final result
    let mut res: MultiMap<Id, Rc<Entry>> = MultiMap::default();
    // to prevent repetition in created entries we seperate latest level to make sure at least one
    // will be used
    let mut latest: MultiMap<Id, Rc<Entry>> = MultiMap::default();

    let mut available_edges: MultiMap<Id, &SymbolLang> = MultiMap::default();
    let mut remaining: Vec<(HashSet<Id>, (Id, &SymbolLang))> = Vec::new();
    for c in egraph.classes() {
        for e in c.nodes.iter() {
            if e.children.is_empty() {
                available_edges.insert(c.id, e);
            } else {
                remaining.push((HashSet::from_iter(e.children.iter().copied()), (c.id, e)));
            }
        }
    }

    for i in 0..max_depth {
        let mut new_ids: HashSet<Id> = HashSet::new();
        let mut new_latest: MultiMap<Id, Rc<Entry>> = MultiMap::default();
        for (id, edges) in available_edges.iter_all() {
            edges.iter().for_each(|edge| {
                if !latest.contains_key(&id) && !res.contains_key(&id) {
                    // TODO: should be set
                    &new_ids.insert(*id);
                }

                // if there are no children there won't be children combinations
                if i == 0 && edge.is_leaf() {
                    new_latest.insert(*id, Rc::new(Entry::new(edge, *id, iter::empty())));
                    // res.insert(*id, Rc::new(Entry::new(edge, *id, iter::empty())));
                }

                // TODO: have multiple product functions that use iproduct over iterators instead of vecs

                let mut inp: Vec<(Option<&Vec<Rc<Entry>>>, Option<&Vec<Rc<Entry>>>)> = Vec::new();
                let mut inp_merged: Vec<Vec<Rc<Entry>>> = Vec::new();
                for c in edge.children.iter() {
                    inp.push((latest.get_vec(c), res.get_vec(c)));
                    let mut merged = latest.get_vec(c).map_or_else(|| vec![], |v| v.clone());
                    merged.extend(res.get_vec(c).map_or_else(|| vec![], |v| v.clone()));
                    inp_merged.push(merged);
                }
                let mut entries: Vec<Entry> = Vec::new();
                // To prevent repetition, split into 3 iterators, those without latest, one has to be latest, those that can be both.
                // The first two promise that each combination is created once.
                for i in 0..inp.len() {
                    let mut prelude = inp[0..i].iter().filter_map(|t| t.1).collect_vec();
                    if prelude.len() != i {
                        break;
                    }
                    // current
                    if inp[i].0.is_none() {
                        continue;
                    }
                    prelude.push(inp[i].0.unwrap());
                    // rest
                    let rest: Vec<&Vec<Rc<Entry>>> = inp_merged[i+1..].iter().collect_vec();
                    // Should always have at least one translation here
                    assert_eq!(rest.len(), inp.len() - i - 1);
                    prelude.extend(rest);
                    for children in product(&prelude[..]) {
                        entries.push(Entry::new(edge, *id, children.into_iter().cloned()));
                    }
                }
                for x in entries {
                    new_latest.insert(*id, Rc::new(x));
                }
            })
        };
        let keys = latest.keys().copied().collect_vec();
        for x in keys {
            res.insert_many(x, latest.remove(&x).unwrap());
        }
        latest = new_latest;
        let mut i = 1;
        'outer: while i - 1 < remaining.len() {
            let j = i - 1;
            'inner: for new_id in new_ids.iter() {
                remaining[j].0.remove(new_id);
                if remaining[j].0.is_empty() {
                    available_edges.insert(remaining[j].1 .0, remaining[j].1 .1);
                    remaining.remove(j);
                    i -= 1;
                    break 'inner;
                }
            }
            i += 1;
        }
    }
    let keys = latest.keys().copied().collect_vec();
    for x in keys {
        res.insert_many(x, latest.remove(&x).unwrap());
    }
    return res;
}
