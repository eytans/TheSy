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
use std::collections::{HashSet, HashMap};
use crate::thesy::{TheSy, DataType};
use std::iter::FromIterator;

mod tree;
mod eggstentions;
mod tools;
mod thesy;


fn main() {
    let nat = DataType::new("nat".to_string(), vec![
        "(Z nat)".parse().unwrap(),
        "(S nat nat)".parse().unwrap()
    ]);

    let nat_examples = vec!["Z".parse().unwrap(), "(S Z)".parse().unwrap(), "(S (S Z))".parse().unwrap()];

    let nat_definitions = vec![("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)")].into_iter()
        .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect();

    let mut sygue = TheSy::new(
        nat.clone(),
        nat_examples.clone(),
        nat_definitions,
    );

    let mut nat_rws: Vec<Rewrite<SymbolLang, ()>> = vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")];
    let start = SystemTime::now();
    sygue.run(&mut nat_rws, 2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());

    let list = DataType::new("list".to_string(), vec![
        "(Nil list)".parse().unwrap(),
        "(Cons nat list list)".parse().unwrap()
    ]);

    let list_examples = vec!["Nil".parse().unwrap(), "(Cons x Nil)".parse().unwrap(), "(Cons y (Cons x Nil))".parse().unwrap()];

    let mut sygue = TheSy::new_with_ph(
        vec![list.clone(), nat.clone()],
        // vec![list.clone()],
        HashMap::from_iter(vec![(list, list_examples), (nat, nat_examples)]),
        // HashMap::from_iter(vec![(list, list_examples)]),
        vec![("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)"),
             ("Nil", "list"), ("Cons", "(-> nat list list)"), ("snoc", "(-> list nat list)"),
             ("rev", "(-> list list)"), ("app", "(-> list list list)"),
             ("len", "(-> list nat)")
        ].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
        3
    );

    // sygue.egraph.dot().to_dot("graph.dot");

    let mut list_rws: Vec<Rewrite<SymbolLang, ()>> = vec![
        rewrite!("app base"; "(app Nil ?xs)" => "?xs"),
        rewrite!("app ind"; "(app (Cons ?y ?ys) ?xs)" => "(Cons ?y (app ?ys ?xs))"),
        rewrite!("snoc base"; "(snoc Nil ?x)" => "(Cons ?x Nil)"),
        rewrite!("snoc ind"; "(snoc (Cons ?y ?ys) ?x)" => "(Cons ?y (snoc ?ys ?x))"),
        rewrite!("rev base"; "(rev Nil)" => "Nil"),
        rewrite!("rev ind"; "(rev (Cons ?y ?ys))" => "(snoc (rev ?ys) ?y)"),
        rewrite!("len base"; "(len Nil)" => "Z"),
        rewrite!("len ind"; "(len (Cons ?y ?ys))" => "(S (len ?ys))"),
    ];
    list_rws.extend(nat_rws.into_iter());
    let start = SystemTime::now();
    sygue.run(&mut list_rws, 2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
}
