
use std::borrow::Borrow;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;
use log::{log, warn};

use itertools::{Either, Itertools};
#[cfg(feature = "stats")]
use serde_json;
use structopt::StructOpt;

use egg::*;

use egg::pretty_string::PrettyString;
use TheSy::thesy::{example_creator};
use TheSy::thesy::case_split::{CaseSplit, Split};
use TheSy::thesy::thesy::TheSy as Synth;
use TheSy::thesy::semantics::Definitions;
use TheSy::{SubCmd, thesy, TheSyConfig};
use egg::tools::tools::choose;
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
    /// Run exploration, as a prover, check equivalence only, or skip case split in equivalence
    /// check
    #[structopt(name = "run mode", short = "m", long = "mode", default_value = "Run")]
    run_mode: SubCmd,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(
            Definitions::from_file(&opts.path),
            opts.ph_count,
            vec![],
            opts.path.with_extension("res.th"),
            opts.run_mode,
        )
    }
}

fn main() {
    use simplelog::*;

    let args: CliOpt = CliOpt::from_args();

    let log_path = args.path.with_extension("log");
    let mut thesy_config: simplelog::Config = ConfigBuilder::new().add_filter_ignore_str("egg").build();
    let mut egg_config: simplelog::Config = ConfigBuilder::new().add_filter_allow_str("egg").build();
    CombinedLogger::init(
        vec![
            TermLogger::new(LevelFilter::Debug, thesy_config, TerminalMode::Mixed, ColorChoice::Auto),
            TermLogger::new(LevelFilter::Warn, egg_config, TerminalMode::Mixed, ColorChoice::Auto),
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
    if args.run_mode.is_check_equiv() || args.run_mode.is_no_case_split() {
        // Shortened mode, only trying short proof of goals without exploration
        if args.run_mode.is_no_case_split() {
            for (vars, holes, precond, ex1, ex2) in &config.definitions.conjectures {
                if !Synth::check_equality(&rws, precond, ex1, ex2) {
                    println!("Failed to prove conjecture {} => {} = {}",
                             precond.clone().map(|p| p.pretty(500)).unwrap_or("true".to_string()),
                             ex1.pretty(500), ex2.pretty(500));
                    exit(1);
                }
            }
        } else {
            // We are in case split mode
            let (mut thesy, mut case_split, mut rules) = config.create_thesy();
            let res = thesy.check_goals(&mut Some(&mut case_split), &mut rules);
            if !thesy.remaining_goals().unwrap().is_empty() {
                println!("Failed to prove conjectures");
                exit(1);
            }
        }
        warn!("Finished proving all goals in {:?}", start.elapsed().unwrap());
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
fn export_json(thesy: &thesy::TheSy, path: &PathBuf) {
    let stat_path = path.with_extension("stats.json");
    serde_json::to_writer(File::create(stat_path).unwrap(), &thesy.stats);
}

#[cfg(not(feature = "stats"))]
fn export_json(thesy: &TheSy::thesy::thesy::TheSy, path: &PathBuf) {}
