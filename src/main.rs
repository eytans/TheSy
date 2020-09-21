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
        DataType::new("nat".to_string(), vec![
            "(Z nat)".parse().unwrap(),
            "(S nat nat)".parse().unwrap()
        ]),
        vec!["Z".parse().unwrap(), "(S Z)".parse().unwrap(), "(S (S Z))".parse().unwrap()],
        vec![("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)")].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
    );

    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    let start = SystemTime::now();
    sygue.run(&mut rewrites,2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());

    let mut sygue = TheSy::new(
        DataType::new("list".to_string(), vec![
            "(Nil list)".parse().unwrap(),
            "(Cons nat list list)".parse().unwrap()
        ]),
        vec!["Nil".parse().unwrap(), "(Cons x Nil)".parse().unwrap(), "(Cons y (Cons x Nil))".parse().unwrap()],
        vec![("Nil", "list"), ("Cons", "(-> nat list list)"), ("snoc", "(-> list nat list)"), ("rev", "(-> list list)"), ("app", "(-> list list list)")].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
    );

    sygue.egraph.dot().to_dot("graph.dot");

    let mut rewrites: Vec<Rewrite<SymbolLang, ()>> = vec![
        rewrite!("app base"; "(app Nil ?xs)" => "?xs"),
        rewrite!("app ind"; "(app (Cons ?y ?ys) ?xs)" => "(Cons ?y (app ?ys ?xs))"),
        rewrite!("snoc base"; "(snoc Nil ?x)" => "(Cons ?x Nil)"),
        rewrite!("snoc ind"; "(snoc (Cons ?y ?ys) ?x)" => "(Cons ?y (snoc ?ys ?x))"),
        rewrite!("rev base"; "(rev Nil)" => "Nil"),
        rewrite!("rev ind"; "(rev (Cons ?y ?ys))" => "(snoc (rev ?ys) ?y)"),
    ];
    let start = SystemTime::now();
    sygue.run(&mut rewrites,2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
}
