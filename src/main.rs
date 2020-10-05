// #![feature(iterator_fold_self)]
#[macro_use(rewrite)]
extern crate egg;

use std::borrow::Borrow;
use std::fs::File;
use std::io::{Write};
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;

use egg::*;
use itertools::Itertools;
use structopt::StructOpt;

use crate::thesy::thesy::TheSy;
use crate::thesy::thesy_parser::parser::Definitions;
use crate::tools::tools::choose;
use crate::thesy::{thesy_parser, example_creator};

mod eggstentions;
mod tools;
mod thesy;
mod lang;
mod tree;
// mod smtlib_translator;

/// Arguments to use to run thesy
#[derive(StructOpt)]
struct CliOpt {
    /// The path to the file to read
    #[structopt(parse(from_os_str))]
    path: std::path::PathBuf,
    /// Placeholder count
    #[structopt(name = "placeholder count", default_value = "2")]
    ph_count: usize,
    /// Previous results to read
    dependencies: Vec<String>,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(
            thesy_parser::parser::parse_file(opts.path.to_str().unwrap().to_string()),
            opts.ph_count,
            vec![],
            opts.path.with_extension("res.th"))
    }
}

#[derive(Debug, Clone)]
struct TheSyConfig {
    definitions: Definitions,
    ph_count: usize,
    dependencies: Vec<TheSyConfig>,
    dep_results: Vec<Vec<Rewrite<SymbolLang, ()>>>,
    output: PathBuf,
    prerun: bool,
}

impl TheSyConfig {
    pub fn new(definitions: Definitions, ph_count: usize, dependencies: Vec<TheSyConfig>, output: PathBuf) -> TheSyConfig {
        let func_len = definitions.functions.len();
        TheSyConfig {
            definitions,
            ph_count,
            dependencies,
            dep_results: vec![],
            output,
            prerun: false,
        }
        // prerun: func_len > 2}
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
        TheSyConfig::new(definitions, 2, vec![], PathBuf::from(path).with_extension("res"))
    }

    /// Run thesy using current configuration returning (thesy instance, previous + new rewrites)
    pub fn run(&mut self, max_depth: Option<usize>) -> (TheSy, Vec<Rewrite<SymbolLang, ()>>) {
        self.collect_dependencies();
        let mut rules = self.definitions.rws.clone();
        rules.extend(self.dep_results.iter().flatten().cloned());
        // Prerun helps prevent state overflow
        if self.prerun && self.definitions.functions.len() > 2 {
            for f in &self.definitions.functions {
                println!("prerun {}", f.name);
                let mut new_conf = self.clone();
                let funcs = vec![f.clone()];
                new_conf.definitions.functions = funcs;
                let mut thesy = TheSy::from(&new_conf);
                thesy.run(&mut rules, max_depth.unwrap_or(2));
            }
            for couple in choose(&self.definitions.functions[..], 2) {
                println!("prerun {}", couple.iter().map(|x| &x.name).join(" "));
                let mut new_conf = self.clone();
                let funcs = couple.into_iter().cloned().collect_vec();
                new_conf.definitions.functions = funcs;
                let mut thesy = TheSy::from(&new_conf);
                thesy.run(&mut rules, max_depth.unwrap_or(2));
            }
        }
        let mut thesy = TheSy::from(self.borrow());
        let results = thesy.run(&mut rules, max_depth.unwrap_or(2));
        let new_rules_text = results.iter()
            .map(|(searcher, applier, rw)|
                format!("(=> \"{} => {}\" {} {})", searcher.pretty(1000), applier.pretty(1000), searcher.pretty(1000), applier.pretty(1000)))
            .join("\n");
        File::create(&self.output).unwrap().write_all(new_rules_text.as_bytes()).unwrap();
        (thesy, rules)
    }
}

impl From<&TheSyConfig> for TheSy {
    fn from(conf: &TheSyConfig) -> Self {
        let mut dict = conf.definitions.functions.clone();
        for c in conf.definitions.datatypes.iter().flat_map(|d| &d.constructors) {
            dict.push(c.clone());
        }
        let examples = conf.definitions.datatypes.iter()
            .map(|d| (d.clone(), example_creator::examples(d, 2)))
            .collect();
        TheSy::new_with_ph(conf.definitions.datatypes.clone(),
                           examples,
                           dict,
                           conf.ph_count,
                           Some(conf.definitions.conjectures.clone()))
    }
}

fn main() {
    let args = CliOpt::from_args();
    let start = SystemTime::now();
    // TODO: Add logging of all runs
    let res = TheSyConfig::from(&args).run(Some(2));
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    exit(0);
}
