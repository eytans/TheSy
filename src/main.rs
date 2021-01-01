#[macro_use(rewrite)]
extern crate egg;

#[macro_use]
extern crate log;
extern crate simplelog;

#[macro_use]
extern crate global_counter;

#[macro_use]
extern crate lazy_static;

use std::borrow::Borrow;
use std::fs::File;
use std::io::{Write};
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;

use egg::*;
use itertools::{Itertools, Either};
use structopt::StructOpt;

use crate::thesy::thesy::TheSy;
use crate::thesy::thesy_parser::parser::Definitions;
use crate::tools::tools::choose;
use crate::thesy::{thesy_parser, example_creator};
use crate::eggstentions::pretty_string::PrettyString;

#[cfg(feature = "stats")]
use serde_json;
use crate::thesy::case_split::{CaseSplit, Split};

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
    /// Run as prover or ignore goals
    #[structopt(name = "proof mode", short = "p", long = "prove")]
    proof_mode: Option<bool>,
    #[structopt(name = "check equivalence", short = "c", long = "check-equiv")]
    check_equiv: bool,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(
            thesy_parser::parser::parse_file(opts.path.to_str().unwrap().to_string()),
            opts.ph_count,
            vec![],
            opts.path.with_extension("res.th"),
            opts.proof_mode.unwrap_or(true),
        )
    }
}

#[derive(Clone)]
struct TheSyConfig {
    definitions: Definitions,
    ph_count: usize,
    dependencies: Vec<TheSyConfig>,
    dep_results: Vec<Vec<Rewrite<SymbolLang, ()>>>,
    output: PathBuf,
    prerun: bool,
    proof_mode: bool,
}

impl TheSyConfig {
    pub fn new(definitions: Definitions, ph_count: usize, dependencies: Vec<TheSyConfig>, output: PathBuf, proof_mode: bool) -> TheSyConfig {
        let func_len = definitions.functions.len();
        TheSyConfig {
            definitions,
            ph_count,
            dependencies,
            dep_results: vec![],
            output,
            prerun: false,
            proof_mode,
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
        TheSyConfig::new(definitions, 2, vec![], PathBuf::from(path).with_extension("res"), true)
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
                let case_split = new_conf.translate_splitters();
                thesy.run(&mut rules, Some(case_split), max_depth.unwrap_or(2));
            }
            for couple in choose(&self.definitions.functions[..], 2) {
                println!("prerun {}", couple.iter().map(|x| &x.name).join(" "));
                let mut new_conf = self.clone();
                let funcs = couple.into_iter().cloned().collect_vec();
                new_conf.definitions.functions = funcs;
                let mut thesy = TheSy::from(&new_conf);
                let case_split = new_conf.translate_splitters();
                thesy.run(&mut rules, Some(case_split), max_depth.unwrap_or(2));
            }
        }
        let mut thesy = TheSy::from(self.borrow());
        let case_split = self.translate_splitters();
        let results = thesy.run(&mut rules, Some(case_split), max_depth.unwrap_or(2));
        let new_rules_text = results.iter()
            .map(|(precond, searcher, applier, rw)|
                if precond.is_some() {
                    let precond = precond.as_ref().unwrap();
                    format!("(=> \"{} |> {} => {}\" (=> {} (= {} {})))", precond.pretty_string(), searcher.pretty(1000), applier.pretty(1000), precond.pretty_string(), searcher.pretty(1000), applier.pretty(1000))
                } else {
                    format!("(=> \"{} => {}\" {} {})", searcher.pretty(1000), applier.pretty(1000), searcher.pretty(1000), applier.pretty(1000))
                })
            .join("\n");
        File::create(&self.output).unwrap().write_all(new_rules_text.as_bytes()).unwrap();
        (thesy, rules)
    }

    pub fn translate_splitters(&self) -> CaseSplit {
        CaseSplit::new(self.definitions.case_splitters.iter().cloned()
            .map(|(searcher, root_var, split_exprs)| {
                let applier: Box<dyn FnMut(&mut EGraph<SymbolLang, ()>, SearchMatches) -> Vec<Split>> =
                    Box::new(move |graph: &mut EGraph<SymbolLang, ()>, m: SearchMatches| {
                        m.substs.iter().map(|s| Split::new(
                            *s.get(root_var).unwrap(),
                            split_exprs.iter().map(|p| {
                                let rec_expr = p.ast.as_ref().iter().map(|node| match node {
                                    ENodeOrVar::ENode(n) => { itertools::Either::Left(n) }
                                    ENodeOrVar::Var(v) => { itertools::Either::Right(*s.get(v.clone()).unwrap()) }
                                });
                                let mut res = vec![];
                                for n in rec_expr {
                                    match n {
                                        Either::Left(n) => {
                                            let mut node = n.clone();
                                            node.update_children(|c| res[usize::from(c)]);
                                            res.push(graph.add(node));
                                        }
                                        Either::Right(id) => {
                                            res.push(id);
                                        }
                                    }
                                }
                                *res.last().unwrap()
                            }).collect_vec(),
                        )).collect_vec()
                    });
                    (searcher, applier)
            }).collect_vec())
    }
}

impl From<&TheSyConfig> for TheSy {
    fn from(conf: &TheSyConfig) -> Self {
        let mut dict = conf.definitions.functions.clone();
        for c in conf.definitions.datatypes.iter().flat_map(|d| &d.constructors) {
            dict.push(c.clone());
        }
        let examples = conf.definitions.datatypes.iter()
            .map(|d| (d.clone(), example_creator::Examples::new(d, 2)))
            .collect();
        let conjectures = if conf.definitions.conjectures.is_empty() {
            None
        } else {
            Some(conf.definitions.conjectures.clone())
        };

        TheSy::new_with_ph(conf.definitions.datatypes.clone(),
                           examples,
                           dict,
                           conf.ph_count,
                           if conf.proof_mode { conjectures } else { None })
    }
}

fn main() {
    use simplelog::*;

    let args = CliOpt::from_args();

    let log_path = args.path.with_extension("log");
    CombinedLogger::init(
        vec![
            TermLogger::new(LevelFilter::Warn, Config::default(), TerminalMode::Mixed),
            WriteLogger::new(LevelFilter::Info, Config::default(), File::create(log_path).unwrap()),
        ]
    ).unwrap();

    if cfg!(feature = "stats") {
        println!("Collecting statistics");
    }

    let start = SystemTime::now();
    let mut config = TheSyConfig::from(&args);
    let thesy = TheSy::from(&config);
    let mut rws = thesy.system_rws.clone();
    rws.extend_from_slice(&config.definitions.rws);
    if args.check_equiv {
        for (vars, precond, ex1, ex2) in &config.definitions.conjectures {
            if TheSy::check_equality(&rws, precond, ex1, ex2) {
                println!("proved: {}{} = {}", precond.as_ref().map(|x| format!("{} => ", x.pretty(500))).unwrap_or("".to_string()), ex1.pretty(500), ex2.pretty(500))
            }
        }
        exit(0)
    }
    let res = config.run(Some(2));
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    if cfg!(feature = "stats") {
        export_json(&res.0, &args.path);
    }
    exit(0);
}

#[cfg(feature = "stats")]
fn export_json(thesy: &TheSy, path: &PathBuf) {
    let stat_path = path.with_extension("stats.json");
    serde_json::to_writer(File::create(stat_path).unwrap(), &thesy.stats);
}

#[cfg(not(feature = "stats"))]
fn export_json(thesy: &TheSy, path: &PathBuf) {}