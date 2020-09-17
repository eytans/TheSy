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
use crate::thesy::{TheSy, DataType};

mod tree;
mod eggstentions;
mod tools;
mod thesy;


fn main() {
    let mut sygue = TheSy::new(
        vec![DataType::new("nat".to_string(), vec![
            Tree::from_str("(Z nat)").unwrap(),
            Tree::from_str("(S nat nat)").unwrap()
        ])],
        vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        vec!["(typed ts_ph0 nat)", "(typed ts_ph1 nat)", "(typed Z nat)", "(typed S (-> nat nat))", "(typed pl (-> nat nat nat))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
    );

    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    let start = SystemTime::now();
    sygue.run(&mut rewrites,3);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
}
