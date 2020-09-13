// #![feature(iterator_fold_self)]
#[macro_use(c)]
extern crate cute;

use std::{iter};

use egg::*;

use crate::tree::Tree;
use std::str::FromStr;
use crate::eggstentions::multisearcher::multisearcher::MultiDiffSearcher;
use itertools::{Itertools, all};
use crate::eggstentions::appliers::DiffApplier;
use crate::eggstentions::reconstruct::reconstruct_all;
use std::time::{Duration, SystemTime};
use std::rc::Rc;
use std::hash::Hash;
use std::collections::HashSet;
use std::iter::FromIterator;
use crate::thesy::SyGuESOE;

mod tree;
mod eggstentions;
mod tools;
mod thesy;


fn main() {
    let mut sygue = SyGuESOE::new(
        vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        vec!["(typed ph0 int)", "(typed ph1 int)", "(typed Z int)", "(typed S (-> int int))", "(typed pl (-> int int int))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
    );

    let start = SystemTime::now();
    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    println!("increase depth 1");
    sygue.increase_depth();
    sygue.egraph.rebuild();
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    // println!("{}", all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    sygue.equiv_reduc(&rewrites[..]);
    // let all_trees = reconstruct_all(&sygue.egraph, 4).values().flatten().cloned().collect_vec();
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    sygue.egraph.rebuild();
    let all_trees = reconstruct_all(&sygue.egraph, 2).iter().flat_map(|x| x.1).cloned().collect::<HashSet<Rc<Tree>>>();
    // println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    println!("{}", all_trees.len());
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    println!("increase depth 2");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    let all_trees = reconstruct_all(&sygue.egraph, 3).iter().flat_map(|x| x.1).cloned().collect::<HashSet<Rc<Tree>>>();
    println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    sygue.egraph.rebuild();
    let all_trees = reconstruct_all(&sygue.egraph, 3).iter().flat_map(|x| x.1).cloned().collect_vec();
    println!("{}", all_trees.into_iter().map(|t| t.to_sexp_string()).intersperse(" ".parse().unwrap()).collect::<String>());
    println!("increase depth 3");
    sygue.increase_depth();
    sygue.equiv_reduc(&rewrites[..]);
    println!("Current time: {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    // let e: Extractor<AstSize, SymbolLang, ()> = Extractor::new(&runner.egraph);
}
