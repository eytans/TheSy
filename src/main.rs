use cached::proc_macro::cached;
use egg::*;
use std::collections::{HashMap, HashSet, LinkedList};
use std::iter::FromIterator;
use std::fmt::{Display, Formatter};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::cmp::Eq;


// fn reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     inner_reconstruct(egraph, id, HashSet::default())
// }
//
// fn inner_reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id, used: HashSet<Id>) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     let updated_id = egraph.find(id);
//     let class = egraph.classes().find(|e| e.id == updated_id).expect("Id shouldn't be deleted");
//     class.nodes.iter().flat_map(|s| )
// }

//  #[cached]
// fn entry_to_tree(root: String, subentries: Vec<Entry>) -> Tree {
//     return Tree::new(
//         root,
//         Vec::from_iter(
//             subentries.iter().map(|x| entry_to_tree(
//                 x.symbol.op.to_string(),
//                 x.subentries.clone()))
//         )
//     );
// }
//
// #[derive(PartialEq, Eq, Clone, Hash)]
// struct Entry {
//     symbol: SymbolLang,
//     subentries: Vec<Entry>
// }
//
// impl Entry {
//     pub fn tree(&self) -> Tree {
//         return entry_to_tree(self.symbol.op.to_string(), self.subentries.clone());
//     }
// }
//
// fn combinations<T>(sets: &[HashSet<T>]) -> Vec<Vec<&T>> {
//     if (sets.len() == 1) {
//         return sets[0].iter().map(|t| vec![t]).collect();
//     }
//
//     let rec_res = combinations(&sets[1..sets.len()]);
//     // TODO: clone iterator
//     let initial_set = sets[0].iter();
//     let add_to_all_combs = initial_set.flat_map(|s| rec_res.iter().map(|v| {
//         let mut v_res = v.to_vec();
//         v_res.insert(0, s);
//         v_res
//     }));
//     return add_to_all_combs.collect::<Vec<Vec<&T>>>();
// }
//
// fn reconstruct_all(egraph: &EGraph<SymbolLang, ()>, max_depth: usize) -> HashMap<Id, HashSet<Tree>> {
//     let mut res: HashMap<Id, HashSet<Tree>> = HashMap::default();
//     for _ in 0..max_depth {
//         egraph.classes()
//             .flat_map(|c| c.nodes.iter()
//                 .filter(|n| n.children.iter()
//                     .all(|child| res.contains_key(child))
//                 ).zip([c.id].iter().cycle())
//             )
//             .for_each(|(n, id)| {
//                 if (!res.contains_key(id)) {
//                     res[id] = HashSet::default();
//                 }
//                 if (n.is_leaf()) {
//                     res[id].insert(Tree::leaf(n.op.to_string()));
//                 }
//                 let children_sets  = n.children.iter().map(|c: &Id| {
//                     let t = res.get(c).unwrap();
//                     return t;
//                 }).collect();
//                 for children in combinations(&children_sets) {
//                     res[id].insert(Tree::new(n.op.to_string(), children.map(|x| x.clone())))
//                 }
//             });
//     }
//     return res;
// }

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
    if size == 0 || size < vec.len() {
        return Vec::default();
    }

    let mut res = Vec::default();
    for (i, k) in vec.iter().enumerate() {
        let mut rec_res = choose(&vec[i+1..], size - 1);
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
        let mut res = if op_res.is_none() {RecExpr::default()} else {op_res.unwrap()};
        return match self {
            Tree::Leaf(r, t) => {
                (res.add(SymbolLang::leaf(r)), res)
            },
            Tree::Branch(r, ss, t) => {
                let mut ids = Vec::default();
                for s in ss {
                    let (id, r) = s.to_rec_expr(Some(res));
                    res = r;
                    ids.push(id);
                }
                (res.add(SymbolLang::new(r, ids)), res)
            },
        }
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

// TODO: hide structs inside mod to hide privates?

#[derive(Clone)]
struct SyGuESOE {
    // TODO: automatic examples
    examples: Vec<Tree>,
    dict: Vec<Tree>,
    ind_ph: Tree,
    egraph: EGraph<SymbolLang, ()>,
    terms: HashMap<Tree, Vec<(Tree, Id)>>
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
        SyGuESOE{
            examples,
            dict,
            ind_ph,
            egraph,
            terms
        }
    }

    fn increase_depth(&self) {
        for val_set in self.terms.values() {

        }
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
// note that if you add the same thing to an e-graph twice, you'll get back equivalent Ids
    assert_eq!(foo2, foo3);
    // let res = reconstruct_all(&egraph, 3);
    // for x in res.values() {
    //     println!("{}", x.iter().collect());
    // }
}
