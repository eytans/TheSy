// #![feature(iterator_fold_self)]
#[macro_use(rewrite)]
extern crate egg;

#[macro_use(c)]
extern crate cute;

use egg::*;

use crate::tree::Tree;
use std::str::FromStr;
use itertools::{Itertools};
use crate::eggstentions::reconstruct::reconstruct_all;
use std::time::{SystemTime};
use std::rc::Rc;
use std::collections::HashSet;
use crate::thesy::{SyGuESOE, DataType};

mod tree;
mod eggstentions;
mod tools;
mod thesy;


fn main() {
    let mut sygue = SyGuESOE::new(
        vec![DataType::new("nat".to_string(), vec![
            Tree::from_str("(Z nat)").unwrap(),
            Tree::from_str("(S nat nat)").unwrap()
        ])],
        vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        vec!["(typed ts_ph0 nat)", "(typed ts_ph1 nat)", "(typed Z nat)", "(typed S (-> nat nat))", "(typed pl (-> nat nat nat))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
    );

    let start = SystemTime::now();
    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    println!("increase depth 1");
    sygue.increase_depth();
    // let all_trees = reconstruct_all(&sygue.egraph, 2).values().flatten().cloned().collect_vec();
    // let mut all_known = HashSet::new();
    // for tree in all_trees.iter() {
    //         assert!(!all_known.contains(&tree));
    //         all_known.insert(tree);
    //     }
    // println!("{}", &all_trees.iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // println!("{}", &all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    sygue.equiv_reduc(&rewrites[..]);
    // let all_trees = reconstruct_all(&sygue.egraph, 4).values().flatten().cloned().collect_vec();
    // println!("{}", &all_trees.iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // let all_trees = reconstruct_all(&sygue.egraph, 2).iter().flat_map(|x| x.1).cloned().collect::<HashSet<Rc<Tree>>>();
    // println!("{}", &all_trees.iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // println!("{}", &all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    println!("increase depth 2");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let all_trees = reconstruct_all(&sygue.egraph, 3).iter().flat_map(|x| x.1).cloned().collect::<HashSet<Rc<Tree>>>();
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // let all_trees = reconstruct_all(&sygue.egraph, 3).iter().flat_map(|x| x.1).cloned().collect_vec();
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    println!("increase depth 3");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let e: Extractor<AstSize, SymbolLang, ()> = Extractor::new(&runner.egraph);
}
