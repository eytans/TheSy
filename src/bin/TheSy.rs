
use std::borrow::Borrow;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;
use log::warn;

use itertools::{Either, Itertools};
#[cfg(feature = "stats")]
use serde_json;
use structopt::StructOpt;

use egg::*;

use TheSy::eggstentions::pretty_string::PrettyString;
use TheSy::thesy::{example_creator};
use TheSy::thesy::case_split::{CaseSplit, Split};
use TheSy::thesy::thesy::TheSy as Synth;
use TheSy::thesy::semantics::Definitions;
use TheSy::TheSyConfig;
use TheSy::tools::tools::choose;
use std::rc::Rc;

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
    /// Run as prover or ignore goals, true if flag is present
    #[structopt(name = "proof mode", short = "p", long = "prove")]
    proof_mode: bool,
    #[structopt(name = "check equivalence", short = "c", long = "check-equiv")]
    check_equiv: bool,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(
            Definitions::from_file(&opts.path),
            opts.ph_count,
            vec![],
            opts.path.with_extension("res.th"),
            opts.proof_mode,
        )
    }
}

fn main() {
    use simplelog::*;

    let args = CliOpt::from_args();

    let log_path = args.path.with_extension("log");
    CombinedLogger::init(
        vec![
            TermLogger::new(LevelFilter::Debug, Config::default(), TerminalMode::Mixed, ColorChoice::Auto),
            WriteLogger::new(LevelFilter::Info, Config::default(), File::create(log_path).unwrap()),
        ]
    ).unwrap();

    if cfg!(feature = "stats") {
        warn!("Collecting statistics");
    }

    let start = SystemTime::now();
    let mut config = TheSyConfig::from(&args);
    let thesy = Synth::from(&config);
    let mut rws = thesy.system_rws.clone();
    rws.extend_from_slice(&config.definitions.rws);
    if args.check_equiv {
        for (vars, holes, precond, ex1, ex2) in &config.definitions.conjectures {
            if Synth::check_equality(&rws, precond, ex1, ex2) {
                println!("proved: Forall {}. {}{} = {}", holes.iter().join(", "), precond.as_ref().map(|x| format!("{} => ", x.pretty(500))).unwrap_or("".to_string()), ex1.pretty(500), ex2.pretty(500))
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
fn export_json(thesy: &TheSy::thesy::thesy::TheSy, path: &PathBuf) {}
