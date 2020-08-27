use cached::proc_macro::cached;
use egg::*;
use std::collections::{HashMap, HashSet, LinkedList};
use std::iter::FromIterator;
use std::fmt::{Display, Formatter, Result};
use std::{fmt, iter};
use std::hash::{Hash, Hasher};
use std::cmp::Eq;
use itertools::Itertools;
use itertools::iproduct;


// fn reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     inner_reconstruct(egraph, id, HashSet::default())
// }
//
// fn inner_reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id, used: HashSet<Id>) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     let updated_id = egraph.find(id);
//     let class = egraph.classes().find(|e| e.id == updated_id).expect("Id shouldn't be deleted");
//     class.nodes.iter().flat_map(|s| )
// }

#[cached]
fn entry_to_tree(root: String, subentries: Vec<Entry>) -> Tree {
    return Tree::Branch(
        root,
        Vec::from_iter(
            subentries.iter().map(|x| entry_to_tree(
                x.symbol.op.to_string(),
                x.subentries.clone()))
        ),
        Box::new(None),
    );
}

#[derive(PartialEq, Eq, Clone, Hash)]
struct Entry {
    symbol: SymbolLang,
    subentries: Vec<Entry>,
}

impl Entry {
    pub fn tree(&self) -> Tree {
        return entry_to_tree(self.symbol.op.to_string(), self.subentries.clone());
    }
}

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
                    res.get_mut(&id).unwrap().insert(Tree::Leaf(edge.op.to_string(), Box::new(None)));
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
                    let new_tree = Tree::Branch(edge.op.to_string(),
                                                updated_children,
                                                Box::new(None));
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

#[derive(Clone, Hash, PartialEq, Eq)]
enum Tree {
    // Root subtrees type
    Leaf(String, Box<Option<Tree>>),
    Branch(String, Vec<Tree>, Box<Option<Tree>>),
}

impl Tree {
    fn to_rec_expr(&self, op_res: Option<RecExpr<SymbolLang>>) -> (Id, RecExpr<SymbolLang>) {
        let mut res = if op_res.is_none() { RecExpr::default() } else { op_res.unwrap() };
        return match self {
            Tree::Leaf(r, t) => {
                (res.add(SymbolLang::leaf(r)), res)
            }
            Tree::Branch(r, ss, t) => {
                let mut ids = Vec::default();
                for s in ss {
                    let (id, r) = s.to_rec_expr(Some(res));
                    res = r;
                    ids.push(id);
                }
                (res.add(SymbolLang::new(r, ids)), res)
            }
        };
    }

    fn add_to_graph(&self, graph: &mut EGraph<SymbolLang, ()>) {
        graph.add_expr(&self.to_rec_expr(None).1);
    }

    fn is_leaf(&self) -> bool {
        match self {
            Tree::Leaf(_, _) => true,
            _ => false,
        }
    }
}

impl Display for Tree {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            Tree::Leaf(r, t) => {
                write!(f, "{}()", r)
            },
            Tree::Branch(r, ss, t) => {
                if ss.is_empty() {write!(f, "{}()", r)}
                else {
                    write!(f, "{}({}", r, ss[0]);
                    for s in ss.iter().skip(1) {
                        write!(f, ", {}", s);
                    }
                    write!(f, ")")
                }
            },
        }
    }
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
    // TODO: ind from example types
    fn new(examples: Vec<Tree>, dict: Vec<Tree>) -> SyGuESOE {
        let ind_ph = Tree::Leaf(String::from("ind_var"), Box::new(Some(Tree::Leaf(String::from("int"), Box::new(None)))));
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

    fn increase_depth(&self) {
        for val_set in self.terms.values() {}
    }
}

fn main() {
// we can do the same thing with an EGraph
    let mut egraph: EGraph<SymbolLang, ()> = Default::default();
    let a: Id = egraph.add(SymbolLang::leaf("a"));
    let b = egraph.add(SymbolLang::leaf("b"));
    let foo = egraph.add(SymbolLang::new("foo", vec![a, b]));

// we can also add RecExprs to an egraph
    let mut expr = RecExpr::default();
    let a = expr.add(SymbolLang::leaf("a"));
    let b = expr.add(SymbolLang::leaf("b"));
    let foo = expr.add(SymbolLang::new("foo", vec![a, b]));
    let foo2 = egraph.add_expr(&expr);
    println!("{}", expr.pretty(10));
    let foo4 = expr.add(SymbolLang::new("bar", vec![a, b]));
    println!("{}", expr.pretty(10));
    let mut cloned = expr.clone();
    println!("{}", cloned.pretty(10));
    let foo3 = cloned.add(SymbolLang::new("bar", vec![a, b]));
    println!("{}", cloned.pretty(10));
    let foo2 = egraph.add_expr(&cloned);
    let recs = reconstruct_all(&egraph, 3);
    for (id, set) in recs.iter() {
        println!("{}", id);
        for t in set {
            println!("{}", t);
        }
    }
// note that if you add the same thing to an e-graph twice, you'll get back equivalent Ids
    let v1 = vec![1, 2, 3];
    let v2 = vec![4, 5, 6];
    let sets = vec![v1.iter().collect::<HashSet<&i32>>(), v2.iter().collect::<HashSet<&i32>>()];
    let combs = combinations(&sets.iter().collect::<Vec<&HashSet<&i32>>>());
    for v in combs {
        for i in v {
            print!("{}, ", i);
        }
        println!("");
    }
    let v3 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    for v in choose(&v3, 5) {
        for i in v {
            print!("{}, ", i);
        }
        println!("");
    }
    // let res = reconstruct_all(&egraph, 3);
    // for x in res.values() {
    //     println!("{}", x.iter().collect());
    // }
}
