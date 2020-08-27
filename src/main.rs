mod tree;

use egg::*;
use std::collections::{HashMap, HashSet, LinkedList};
use std::iter::FromIterator;
use std::fmt::{Display, Formatter};
use std::{fmt, iter};
use std::hash::{Hash, Hasher};
use std::cmp::Eq;
use itertools::Itertools;
use itertools::iproduct;
use symbolic_expressions::Sexp;
use crate::tree::Tree;


// fn reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     inner_reconstruct(egraph, id, HashSet::default())
// }
//
// fn inner_reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id, used: HashSet<Id>) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     let updated_id = egraph.find(id);
//     let class = egraph.classes().find(|e| e.id == updated_id).expect("Id shouldn't be deleted");
//     class.nodes.iter().flat_map(|s| )
// }



// fn combinations<T: Clone, I: Iterator<Item = T> + Clone>(mut sets: impl Iterator<Item = I>) -> impl Iterator<Item = impl Iterator<Item = T>> {
//     let next = sets.next();
//     if next.is_none() {
//         return iter::once(iter::empty());
//     }
//     let rec_res = combinations(sets);
//     let almost = iproduct!(next.unwrap(), rec_res);
//     almost.map(|x, i| iter::once(x).chain(i))
// }

fn combinations<T: Clone>(sets: &[&HashSet<T>]) -> Vec<Vec<T>> {
    if sets.is_empty() {
        return Vec::new();
    }
    if sets.len() == 1 {
        return sets[0].iter().map(|t| vec![t.clone()]).collect();
    }

    let mut rec_res = combinations(&sets[1..sets.len()]);
    // TODO: clone iterator
    let initial_set = &sets[0];
    let mut res = Vec::new();
    for s in initial_set.iter() {
        for r in rec_res.iter() {
            let mut new_r = r.clone();
            new_r.push(s.clone());
            res.push(new_r)
        }
    }

    return res;
}

fn reconstruct_all(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> HashMap<Id, HashSet<Tree>> {
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

fn create_exprs(egrapg: EGraph<SymbolLang, ()>, depth: usize) {
    let consts = vec!["Z"];
    let funcs = vec!["+", "S"];

    // let exprs: Vec<RecExpr<SymbolLang>> = consts.iter().map(|s| RecExpr::default()
    //     .add(SymbolLang::leaf(s))).collect();

    // for i in 1..=2 {
    //     let newExps =
    //         funcs.iter().flat_map(|e| for i in 0..exprs.len() {
    //             for j in i..exprs.len() {
    //                 exprs[i].
    //             }}).collect();
    // }
}

fn choose<K>(vec: &[K], size: usize) -> Vec<Vec<&K>> {
    if size == 1 {
        let mut res = Vec::default();
        vec.iter().for_each(|k| res.push(vec![k.clone()]));
        return res;
    }
    if size == 0 || size > vec.len() {
        return Vec::default();
    }

    let mut res = Vec::default();
    for (i, k) in vec.iter().enumerate() {
        let mut rec_res = choose(&vec[i + 1..], size - 1);
        for v in rec_res.iter_mut() {
            v.push(k);
        }
        res.extend(rec_res);
    }
    res
}


// TODO: hide structs inside mod to hide privates?

#[derive(Clone)]
struct SyGuESOE {
    // TODO: automatic examples
    examples: Vec<Tree>,
    dict: Vec<Tree>,
    ind_ph: Tree,
    egraph: EGraph<SymbolLang, ()>,
    terms: HashMap<Tree, Vec<(Tree, Id)>>,
}

impl SyGuESOE {
    // fn iterate_ph_vals(&self)

    // TODO: ind from example types
    fn new(examples: Vec<Tree>, dict: Vec<Tree>) -> SyGuESOE {
        let ind_ph = Tree::tleaf(String::from("ind_var"), Box::new(Some(Tree::leaf(String::from("int")))));
        let mut egraph = EGraph::default();
        let mut terms = HashMap::new();
        terms.insert(ind_ph.clone(), Vec::default());
        for e in examples.iter() {
            terms.insert(e.clone(), Vec::default());
        }
        for v in dict.iter().filter(|v| v.is_leaf()) {
            let id = egraph.add_expr(&v.to_rec_expr(None).1);
            terms.get_mut(&ind_ph).unwrap().push((v.clone(), id));
            for e in examples.iter() {
                terms.get_mut(e).unwrap().push((v.clone(), id));
            }
        }
        SyGuESOE {
            examples,
            dict,
            ind_ph,
            egraph,
            terms,
        }
    }

    // fn create_sygue_anchor()

    // fn sygue_rules(&self) -> Vec::<egg::Rewrite<SymbolLang, ()>> {
    //     self.examples.iter().enumerate().flat_map(|(i, e)| {
    //         let anchor =
    //         self.dict.iter().map(|f| {
    //
    //         })
    //     }).collect()
    // }

    fn increase_depth(&self) {

    }
}

fn main() {
    let t: Tree = "(a (typed b int) c)".parse().unwrap();
    println!("{}", t);
    // let mut sygue = SyGuESOE::new(vec!);
}
