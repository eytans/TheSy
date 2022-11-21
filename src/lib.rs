#[macro_use(rewrite)]
extern crate egg;

#[macro_use]
extern crate log;
extern crate simplelog;

#[macro_use]
extern crate global_counter;

#[macro_use]
extern crate lazy_static;

pub mod thesy;
mod lang;
mod tests;
mod utils;

// mod smtlib_translator;

use std::borrow::Borrow;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;

use itertools::{Either, Itertools};
#[cfg(feature = "stats")]
use serde_json;
use structopt::StructOpt;

use egg::*;

use egg::pretty_string::PrettyString;
use crate::thesy::{example_creator};
use crate::thesy::case_split::{CaseSplit, Split};
use crate::thesy::thesy::TheSy;
use thesy::semantics::Definitions;
use egg::tools::tools::choose;
use std::rc::Rc;
pub(crate) use crate::thesy::consts::system_case_splits;

use std::alloc;
use cap::Cap;
use crate::lang::ThRewrite;
use crate::SubCmd::Prove;

pub const PRETTY_W: usize = 500;

#[derive(StructOpt, Clone, Copy, strum_macros::EnumString)]
pub enum SubCmd {
    /// Run thesy
    Run,
    /// Run thesy in proof mode
    Prove,
    /// Check equivalence
    CheckEquiv,
    /// Check equivalence without Case split
    CENoCaseSplit,
}

impl SubCmd {
    pub fn is_run(&self) -> bool {
        match self {
            SubCmd::Run => true,
            _ => false,
        }
    }

    pub fn is_prove(&self) -> bool {
        match self {
            SubCmd::Prove => true,
            _ => false,
        }
    }

    pub fn is_check_equiv(&self) -> bool {
        match self {
            SubCmd::CheckEquiv => true,
            _ => false,
        }
    }

    pub fn is_no_case_split(&self) -> bool {
        match self {
            SubCmd::CENoCaseSplit => true,
            _ => false,
        }
    }
}

#[derive(Clone)]
pub struct TheSyConfig {
    pub definitions: Definitions,
    ph_count: usize,
    dependencies: Vec<TheSyConfig>,
    dep_results: Vec<Vec<ThRewrite>>,
    output: PathBuf,
    prerun: bool,
    run_mode: SubCmd,
}

impl TheSyConfig {
    pub fn new(definitions: Definitions, ph_count: usize, dependencies: Vec<TheSyConfig>, output: PathBuf, run_mode: SubCmd) -> TheSyConfig {
        let func_len = definitions.functions.len();
        TheSyConfig {
            definitions,
            ph_count,
            dependencies,
            dep_results: vec![],
            output,
            prerun: false,
            run_mode,
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
        let definitions = Definitions::from_file(&PathBuf::from(path.clone()));
        TheSyConfig::new(definitions,
                         2,
                         vec![],
                         PathBuf::from(path).with_extension("res"),
                         Prove)
    }

    pub fn create_thesy(&mut self) -> (TheSy, CaseSplit, Vec<ThRewrite>) {
        self.collect_dependencies();
        let mut rules = self.definitions.rws.clone();
        rules.extend(self.dep_results.iter().flatten().cloned());
        let thesy: TheSy = TheSy::from(&*self);
        let case_split =
            TheSy::create_case_splitter(self.definitions.case_splitters.clone());
        (thesy, case_split, rules)
    }

    /// Run thesy using current configuration returning (thesy instance, previous + new rewrites)
    pub fn run(&mut self, max_depth: Option<usize>) -> (TheSy, Vec<ThRewrite>) {
        let (mut thesy, case_split, mut rules) = self.create_thesy();
        // Prerun helps prevent state overflow
        if self.prerun && self.definitions.functions.len() > 2 {
            for f in &self.definitions.functions {
                info!("prerun {}", f.name);
                let mut new_conf = self.clone();
                let funcs = vec![f.clone()];
                new_conf.definitions.functions = funcs;
                let mut thesy = TheSy::from(&new_conf);
                let case_split = TheSy::create_case_splitter(new_conf.definitions.case_splitters);
                thesy.run(&mut rules, Some(case_split), max_depth.unwrap_or(2));
            }
            for couple in choose(&self.definitions.functions[..], 2) {
                info!("prerun {}", couple.iter().map(|x| &x.name).join(" "));
                let mut new_conf = self.clone();
                let funcs = couple.into_iter().cloned().collect_vec();
                new_conf.definitions.functions = funcs;
                let mut thesy = TheSy::from(&new_conf);
                let case_split = TheSy::create_case_splitter(new_conf.definitions.case_splitters);
                thesy.run(&mut rules, Some(case_split), max_depth.unwrap_or(2));
            }
        }
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
}

impl From<&Definitions> for TheSy {
    fn from(defs: &Definitions) -> Self {
        let mut dict = defs.functions.clone();
        for c in defs.datatypes.iter().flat_map(|d| &d.constructors) {
            dict.push(c.clone());
        }
        let examples = defs.datatypes.iter()
            .map(|d| (d.clone(), example_creator::Examples::new(d, 2)))
            .collect();
        let conjectures = if defs.conjectures.is_empty() {
            None
        } else {
            Some(defs.conjectures.clone())
        };

        TheSy::new_with_ph(defs.datatypes.clone(),
                           examples,
                           dict,
                           2,
                           conjectures)
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

        if conf.run_mode.is_run() && conjectures.iter().any(|x| !x.is_empty()) {
            warn!("Running exploration without proof mode, but goals were given");
        }

        TheSy::new_with_ph(conf.definitions.datatypes.clone(),
                           examples,
                           dict,
                           conf.ph_count,
                           if conf.run_mode.is_run() { None } else { conjectures })
    }
}