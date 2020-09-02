// #![feature(iterator_fold_self)]

use std::{iter};
use std::collections::HashMap;

use egg::*;

use crate::tree::Tree;

mod tree;
mod eggstentions;
mod tools;

// fn reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     inner_reconstruct(egraph, id, HashSet::default())
// }
//
// fn inner_reconstruct(egraph: &EGraph<SymbolLang, ()>, id: Id, used: HashSet<Id>) -> impl Iterator<Item = RecExpr<SymbolLang>> {
//     let updated_id = egraph.find(id);
//     let class = egraph.classes().find(|e| e.id == updated_id).expect("Id shouldn't be deleted");
//     class.nodes.iter().flat_map(|s| )
// }

// fn create_exprs(egrapg: EGraph<SymbolLang, ()>, depth: usize) {
    // let consts = vec!["Z"];
    // let funcs = vec!["+", "S"];

    // let exprs: Vec<RecExpr<SymbolLang>> = consts.iter().map(|s| RecExpr::default()
    //     .add(SymbolLang::leaf(s))).collect();

    // for i in 1..=2 {
    //     let newExps =
    //         funcs.iter().flat_map(|e| for i in 0..exprs.len() {
    //             for j in i..exprs.len() {
    //                 exprs[i].
    //             }}).collect();
    // }
// }


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

    fn iterate_ph_vals(&self) -> impl Iterator<Item = &Tree> {
        iter::once(&self.ind_ph).chain(&self.examples)
    }

    fn create_sygue_anchor() {}

    fn sygue_rules(&self) -> Vec::<egg::Rewrite<SymbolLang, ()>> {
        self.iterate_ph_vals().enumerate().flat_map(|(i, e)| {
            let anchor = SyGuESOE::create_sygue_anchor();
            self.dict.iter().map(|f| {
                assert_eq!(f.root, "typed");
                rewrite!(f.to_string(); "?x" => "?x + 1")
            })
        }).collect()
    }

    fn increase_depth(&self) {

    }
}

fn main() {
    let t: Tree = "(a (typed b int) c)".parse().unwrap();
    // let exps_strs = vec!["0", "1", "2", "x", "y", "z", "(+ x y)", "(+ y x)", "(+ x z)", "(+ z x)", "(+ z y)", "(+ y z)", "(+ x x)", "(+ y y)", "(+ z z)", "(s 0)", "(s 1)", "(s 2)", "(s x)", "(s y)", "(s z)", "(s (s 0))", "(s (s 1))", "(s (s 2))", ];

    println!("{}", t);
    // let mut sygue = SyGuESOE::new(vec!);
}
