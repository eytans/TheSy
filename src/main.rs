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
use std::env;
use std::path::PathBuf;
use structopt::StructOpt;
use std::fs::File;
use std::io::{Read, Write};
use crate::thesy_parser::parser::Definitions;
use std::process::exit;
use std::borrow::Borrow;

mod tree;
mod eggstentions;
mod tools;
mod thesy;
mod thesy_parser;

/// Arguments to use to run thesy
#[derive(StructOpt)]
struct CliOpt {
    /// The path to the file to read
    #[structopt(parse(from_os_str))]
    path: std::path::PathBuf,
    /// Placeholder count
    #[structopt(name = "placeholder count", default_value = "3")]
    ph_count: usize,
    /// Previous results to read
    dependencies: Vec<String>,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(thesy_parser::parser::parse_file(opts.path.to_str().unwrap().to_string()), 3, vec![], opts.path.with_extension("res"))
    }
}

struct TheSyConfig {
    definitions: Definitions,
    ph_count: usize,
    dependencies: Vec<TheSyConfig>,
    dep_results: Vec<Vec<Rewrite<SymbolLang, ()>>>,
    output: PathBuf
}

impl TheSyConfig {
    pub fn new(definitions: Definitions, ph_count: usize, dependencies: Vec<TheSyConfig>, output: PathBuf) -> TheSyConfig {
        TheSyConfig { definitions,
            ph_count,
            dependencies,
            dep_results: vec![],
            output}
    }

    fn collect_dependencies(&mut self) {
        if self.dep_results.is_empty() {
            self.dep_results = self.dependencies.iter_mut().map(|conf| {
                conf.run(Some(2)).1
            }).collect_vec();
        }
    }

    pub fn from_path(path: String) -> TheSyConfig {
        let definitions = thesy_parser::parser::parse_file(path.clone());
        TheSyConfig::new(definitions, 3, vec![], PathBuf::from(path).with_extension("res"))
    }

    /// Run thesy using current configuration returning (thesy instance, previous + new rewrites)
    pub fn run(&mut self, max_depth: Option<usize>) -> (TheSy, Vec<Rewrite<SymbolLang, ()>>) {
        self.collect_dependencies();
        let mut thesy = TheSy::from(self.borrow());
        let mut rules = self.definitions.rws.clone();
        rules.extend(self.dep_results.iter().flatten().cloned());
        let results = thesy.run(&mut rules, max_depth.unwrap_or(2));
        let new_rules_text = results.iter()
            .map(|(searcher, applier, rw)|
                format!("{} => {}", searcher.pretty(1000), applier.pretty(1000)))
            .join("\n");
        File::create(&self.output).unwrap().write_all(new_rules_text.as_bytes()).unwrap();
        (thesy, rules)
    }
}

impl From<&TheSyConfig> for TheSy {
    fn from(conf: &TheSyConfig) -> Self {
        let dict = conf.definitions.functions.iter().map(|f| (f.name.clone(), f.get_type())).collect_vec();
        TheSy::new_with_ph(conf.definitions.datatypes.clone(),
                           HashMap::new(),
                           dict,
                           conf.ph_count)
    }
}

fn main() {
    let args = CliOpt::from_args();
    let res = TheSyConfig::from(&args).run(Some(2));

    exit(0);

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
        HashMap::from_iter(vec![(list.clone(), list_examples.clone()), (nat.clone(), nat_examples.clone())]),
        // HashMap::from_iter(vec![(list, list_examples)]),
        vec![("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)"),
             ("Nil", "list"), ("Cons", "(-> nat list list)"), ("snoc", "(-> list nat list)"),
             ("rev", "(-> list list)"), ("app", "(-> list list list)"),
             // ("len", "(-> list nat)"), ("sum", "(-> list nat)"),
             // ("map", "(-> (-> nat nat) list)"), ("fold", "(-> nat (-> nat nat nat) list nat)"),
        ].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
        3,
    );

    sygue.egraph.dot().to_dot("graph.dot");

    let mut list_rws: Vec<Rewrite<SymbolLang, ()>> = vec![
        rewrite!("app base"; "(app Nil ?xs)" => "?xs"),
        rewrite!("app ind"; "(app (Cons ?y ?ys) ?xs)" => "(Cons ?y (app ?ys ?xs))"),
        rewrite!("snoc base"; "(snoc Nil ?x)" => "(Cons ?x Nil)"),
        rewrite!("snoc ind"; "(snoc (Cons ?y ?ys) ?x)" => "(Cons ?y (snoc ?ys ?x))"),
        rewrite!("rev base"; "(rev Nil)" => "Nil"),
        rewrite!("rev ind"; "(rev (Cons ?y ?ys))" => "(snoc (rev ?ys) ?y)"),
        // rewrite!("len base"; "(len Nil)" => "Z"),
        // rewrite!("len ind"; "(len (Cons ?y ?ys))" => "(S (len ?ys))"),
        // rewrite!("sum base"; "(sum Nil)" => "Z"),
        // rewrite!("sum ind"; "(sum (Cons ?y ?ys))" => "(pl ?y (sum ?ys))"),
        // rewrite!("map base"; "(map ?f Nil)" => "Nil"),
        // rewrite!("map ind"; "(map ?f (Cons ?y ?ys))" => "(Cons (apply ?f ?y) (map ?f ?ys))"),
        // rewrite!("fold base"; "(fold ?i ?f Nil)" => "?i"),
        // rewrite!("fold ind"; "(fold ?i ?f (Cons ?y ?ys))" => "(fold (apply ?f ?y ?i) ?f ?ys)"),
    ];
    list_rws.extend(nat_rws.into_iter());
    let start = SystemTime::now();
    let new_rules = sygue.run(&mut list_rws, 2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());


    let mut sygue = TheSy::new_with_ph(
        vec![list.clone(), nat.clone()],
        // vec![list.clone()],
        HashMap::from_iter(vec![(list.clone(), list_examples.clone()), (nat.clone(), nat_examples.clone())]),
        // HashMap::from_iter(vec![(list, list_examples)]),
        vec![("Z", "nat"), ("S", "(-> nat nat)"), ("pl", "(-> nat nat nat)"),
             ("Nil", "list"), ("Cons", "(-> nat list list)"), ("snoc", "(-> list nat list)"),
             ("rev", "(-> list list)"), ("app", "(-> list list list)"),
             ("len", "(-> list nat)"), ("sum", "(-> list nat)"),
             ("map", "(-> (-> nat nat) list)"), ("fold", "(-> nat (-> nat nat nat) list nat)"),
        ].into_iter()
            .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
        2,
    );

    sygue.egraph.dot().to_dot("graph.dot");

    list_rws.extend_from_slice(&vec![
        // rewrite!("app base"; "(app Nil ?xs)" => "?xs"),
        // rewrite!("app ind"; "(app (Cons ?y ?ys) ?xs)" => "(Cons ?y (app ?ys ?xs))"),
        // rewrite!("snoc base"; "(snoc Nil ?x)" => "(Cons ?x Nil)"),
        // rewrite!("snoc ind"; "(snoc (Cons ?y ?ys) ?x)" => "(Cons ?y (snoc ?ys ?x))"),
        // rewrite!("rev base"; "(rev Nil)" => "Nil"),
        // rewrite!("rev ind"; "(rev (Cons ?y ?ys))" => "(snoc (rev ?ys) ?y)"),
        rewrite!("len base"; "(len Nil)" => "Z"),
        rewrite!("len ind"; "(len (Cons ?y ?ys))" => "(S (len ?ys))"),
        rewrite!("sum base"; "(sum Nil)" => "Z"),
        rewrite!("sum ind"; "(sum (Cons ?y ?ys))" => "(pl ?y (sum ?ys))"),
        rewrite!("map base"; "(map ?f Nil)" => "Nil"),
        rewrite!("map ind"; "(map ?f (Cons ?y ?ys))" => "(Cons (apply ?f ?y) (map ?f ?ys))"),
        rewrite!("fold base"; "(fold ?i ?f Nil)" => "?i"),
        rewrite!("fold ind"; "(fold ?i ?f (Cons ?y ?ys))" => "(fold (apply ?f ?y ?i) ?f ?ys)"),
    ]);
    let start = SystemTime::now();
    sygue.run(&mut list_rws, 2);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
}
