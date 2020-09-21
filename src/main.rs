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
            "(Z nat)".parse().unwrap(),
            "(S nat nat)".parse().unwrap()
        ])],
        vec!["Z".parse().unwrap(), "(S Z)".parse().unwrap(), "(S (S Z))".parse().unwrap()],
        vec![("ts_ph0", "nat"), ("ts_ph1", "nat"), ("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)")].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
    );

    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    let start = SystemTime::now();
    sygue.run(&mut rewrites,3);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
}
