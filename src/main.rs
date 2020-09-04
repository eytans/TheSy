// #![feature(iterator_fold_self)]

use std::{iter};
use std::collections::HashMap;

use egg::*;

use crate::tree::Tree;
use std::str::FromStr;
use crate::eggstentions::multisearcher::multisearcher::MultiDiffSearcher;
use itertools::Itertools;
use crate::eggstentions::appliers::DiffApplier;
use crate::eggstentions::reconstruct_all;
use egg::test::run;
use std::time::{Duration, SystemTime};

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

struct SyGuESOE {
    // TODO: automatic examples
    examples: Vec<Tree>,
    dict: Vec<Tree>,
    ind_ph: Tree,
    egraph: EGraph<SymbolLang, ()>,
    // egraph: EGraph<SymbolLang, ()>,
    // terms: HashMap<Tree, Vec<(Tree, Id)>>,
    sygue_rules: Vec<Rewrite<SymbolLang, ()>>,
}

impl SyGuESOE {
    // TODO: ind from example types
    fn new(examples: Vec<Tree>, dict: Vec<Tree>) -> SyGuESOE {
        let ind_ph = Tree::tleaf(String::from("ind_var"), Box::new(Some(Tree::leaf(String::from("int")))));
        let mut egraph = EGraph::default();
        for v in dict.iter().filter(|v| v.subtrees[1].is_leaf()) {
            for (i, e) in Self::iterate_ph_vals(&ind_ph, &examples).enumerate() {
                let anchor = Self::create_sygue_anchor(i);
                egraph.add_expr(&Tree::branch(anchor.clone(), vec![v.subtrees[0].clone()]).to_rec_expr(None).1);
                egraph.add_expr(&Tree::branch(anchor, vec![e.clone()]).to_rec_expr(None).1);
            }
        }
        let mut res = SyGuESOE {
            examples,
            dict,
            ind_ph,
            egraph,
            sygue_rules: vec![],
        };
        let mut rws = res.create_sygue_rules();
        for rw in rws {
            res.sygue_rules.push(rw);
        }
        res
    }

    fn iterate_ph_vals<'a>(ind_ph: &'a Tree, examples: &'a Vec<Tree>) -> impl Iterator<Item=&'a Tree> {
        iter::once(ind_ph).chain(examples)
    }

    fn create_sygue_anchor(i: usize) -> String {
        format!("anchor_{}", i)
    }

    fn iterate_val_cases(&self) -> impl Iterator<Item=&Tree> {
        Self::iterate_ph_vals(&self.ind_ph, &self.examples)
    }

    fn create_sygue_rules(&self) -> Vec::<egg::Rewrite<SymbolLang, ()>> {
        self.iterate_val_cases().enumerate().flat_map(|(i, e)| {
            let anchor = SyGuESOE::create_sygue_anchor(i);
            self.dict.iter().zip(iter::once(anchor).cycle()).filter_map(|(f, anchor)| {
                assert_eq!(f.root, "typed");
                let fun_name = &f.subtrees[0].root;
                let fun_type = &f.subtrees[1];
                if fun_type.root != "->" {
                    None
                } else {
                    let patterns = fun_type.subtrees.iter().take(fun_type.subtrees.len() - 1).enumerate()
                        .flat_map(|(i, t)| {
                            let pat_string = format!("({} ?param_{})", anchor, i);
                            vec![
                                Pattern::from_str(&*pat_string).unwrap(),
                                // Pattern::from_str(&*format!("(typed ?param_{} {})", i, t.to_string())).unwrap(),
                            ]
                        }).collect::<Vec<Pattern<SymbolLang>>>();
                    let searcher = MultiDiffSearcher::new(patterns);
                    let param_list = (0..fun_type.subtrees.len() - 1)
                        .map(|i| format!("?param_{}", i))
                        .intersperse(" ".to_string())
                        .collect::<String>();
                    // TODO: Multiapplier under diffapplier with types at result for lists and trees
                    let applier_string = format!("({} ({} {}))", anchor, fun_name, param_list);
                    let applier = DiffApplier::new(Pattern::from_str(&*applier_string).unwrap());
                    Some(Rewrite::new(fun_name, format!("{}_{}", fun_name, anchor), searcher, applier).unwrap())
                }
            })
        }).collect()
    }

    fn increase_depth(&mut self) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(1).run(&self.sygue_rules).egraph;
    }

    fn equiv_reduc(&mut self, rules: &[Rewrite<SymbolLang, ()>]) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(8).run(rules).egraph;
    }
}

fn main() {
    let t: Tree = "(a (typed b int) c)".parse().unwrap();
    // let exps_strs = vec!["0", "1", "2", "x", "y", "z", "(+ x y)", "(+ y x)", "(+ x z)", "(+ z x)", "(+ z y)", "(+ y z)", "(+ x x)", "(+ y y)", "(+ z z)", "(s 0)", "(s 1)", "(s 2)", "(s x)", "(s y)", "(s z)", "(s (s 0))", "(s (s 1))", "(s (s 2))", ];

    let mut sygue = SyGuESOE::new(
        vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Tree::from_str(s).unwrap()).collect(),
        vec!["(typed ph0 int)", "(typed ph1 int)", "(typed Z int)", "(typed S (-> int int))", "(typed pl (-> int int int))"].into_iter().map(|s| Tree::from_str(s).unwrap()).collect(),
    );

    let all_trees = reconstruct_all(&sygue.egraph, 10).into_iter()
        .flat_map(|x| x.1).collect::<Vec<Tree>>();
    let start = SystemTime::now();
    println!("len of trees {}", all_trees.len());
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    println!("increase depth 1");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let all_trees = reconstruct_all(&sygue.egraph, 10).into_iter()
    //     .flat_map(|x| x.1).collect::<Vec<Tree>>();
    // println!("len of trees {}", all_trees.len());
    // println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    println!("increase depth 2");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    // println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let all_trees = reconstruct_all(&sygue.egraph, 10).into_iter()
    //     .flat_map(|x| x.1).collect::<Vec<Tree>>();
    // println!("len of trees {}", all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    println!("increase depth 3");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    // println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let all_trees = reconstruct_all(&sygue.egraph, 10).into_iter()
    //     .flat_map(|x| x.1).collect::<Vec<Tree>>();
    // println!("len of trees {}", all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    let runner = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(sygue.egraph.clone()).with_iter_limit(8).run(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let all_trees = reconstruct_all(&runner.egraph, 10).into_iter()
    //     .flat_map(|x| x.1).collect::<Vec<Tree>>();
    // println!("previous: 11676, len of trees {}", all_trees.len());
}
