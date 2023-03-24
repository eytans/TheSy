use std::alloc;
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
use TheSy::thesy::{example_creator, prover};
use TheSy::thesy::case_split::{CaseSplit, Split};
use TheSy::thesy::thesy::TheSy as Synth;
use TheSy::thesy::semantics::Definitions;
use TheSy::{CaseSplitConfig, PRETTY_W, SubCmd, thesy, TheSyConfig};
use egg::tools::tools::choose;
use std::rc::Rc;
use cap::Cap;
use TheSy::thesy::statistics::{sample_colored_stats, STATS, StatsReport};

#[global_allocator]
pub(crate) static ALLOCATOR: Cap<alloc::System> = Cap::new(alloc::System, usize::MAX);

/// Arguments to use to run thesy
#[derive(StructOpt, Debug)]
struct CliOpt {
    /// The path to the file to read
    #[structopt(parse(from_os_str))]
    path: PathBuf,
    /// Placeholder count
    #[structopt(name = "placeholder count", short="c", long="phcount", default_value = "2")]
    ph_count: usize,
    /// Run exploration, as a prover, check equivalence only, or skip case split in equivalence
    /// check
    #[structopt(name = "run mode", short = "m", long = "mode", default_value = "Prove")]
    run_mode: SubCmd,
    /// Memory limit in MB
    #[structopt(name = "memory limit", short = "l", long = "limit")]
    mem_limit: Option<usize>,
    /// Case splitter split depth
    #[structopt(name = "case split depth", short = "s", long = "case_split_d")]
    case_split_depth: Option<usize>,
    /// Case splitter split iter num
    #[structopt(name = "case split run amount", short = "i", long = "case_split_i")]
    case_split_itern: Option<usize>,
    /// Number of egg iterations for each depth
    #[structopt(name = "run depth", short = "r", long = "run_depth")]
    run_depth: Option<usize>,
    /// Prover run depth
    #[structopt(name = "prover run depth", short = "p", long = "prover_run_depth")]
    prover_run_depth: Option<usize>,
    /// Prover split depth
    #[structopt(name = "prover split depth", long = "prover_split_d")]
    prover_split_depth: Option<usize>,
    /// Prover split iter num
    #[structopt(name = "prover split run amount", long = "prover_split_i")]
    prover_split_itern: Option<usize>,
    /// Previous results to read
    #[structopt(name = "previous results", long = "prev_res")]
    dependencies: Vec<String>,
}

impl From<&CliOpt> for TheSyConfig {
    fn from(opts: &CliOpt) -> Self {
        TheSyConfig::new(
            Definitions::from_file(&opts.path),
            opts.ph_count,
            vec![],
            opts.path.with_extension("res.th"),
            opts.run_mode,
            opts.run_depth.unwrap_or(thesy::thesy::ITERN),
            CaseSplitConfig::new(
                opts.case_split_depth.unwrap_or(thesy::thesy::EXP_SPLIT_D),
                opts.case_split_itern.unwrap_or(thesy::thesy::EXP_SPLIT_ITERN),
            ),
            opts.prover_run_depth.unwrap_or(prover::RUN_DEPTH),
            CaseSplitConfig::new(
                opts.prover_split_depth.unwrap_or(prover::CASE_SPLIT_DEPTH),
                opts.prover_split_itern.unwrap_or(prover::CASE_ITERN),
            ),
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

    if let Some(limit) = args.mem_limit {
        ALLOCATOR.set_limit(limit * 1024 * 1024).expect("Failed to set memory limit");
    }

    // invariants::set_max_level(invariants::AssertLevel::Off);

    let start = SystemTime::now();
    warn!("CLI Options: {:#?}", args);
    let mut config = TheSyConfig::from(&args);
    warn!("Config: {:#?}", config);
    let thesy = Synth::from(&config);
    let mut rws = thesy.system_rws.clone();
    rws.extend_from_slice(&config.definitions.rws);
    if args.run_mode.is_check_equiv() || args.run_mode.is_no_case_split() {
        // Shortened mode, only trying short proof of goals without exploration
        if args.run_mode.is_no_case_split() {
            for (vars, holes, precond, ex1, ex2) in &config.definitions.conjectures {
                if !Synth::check_equality(&rws, precond, ex1, ex2) {
                    println!("Failed to prove conjecture {} => {} = {}",
                             precond.clone().map(|p| p.pretty(PRETTY_W)).unwrap_or("true".to_string()),
                             ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W));
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
    let mut res = config.run(Some(2));
    #[cfg(all(feature = "split_colored", feature = "stats"))]
    sample_colored_stats(&res.0.egraph, StatsReport::End);
    println!("done in {}", SystemTime::now().duration_since(start).unwrap().as_millis());
    if cfg!(feature = "stats") {
        export_json(&mut res.0, &args.path);
    }
    exit(0);
}

#[cfg(feature = "stats")]
fn export_json(thesy: &mut thesy::TheSy, path: &PathBuf) {
    let stat_path = path.with_extension("stats.json");
    let colored_stat_path = path.with_extension("colored_stats.json");
    thesy.stats.update_mem(&ALLOCATOR);
    serde_json::to_writer(File::create(stat_path).unwrap(), &thesy.stats);
    unsafe {
        serde_json::to_writer(File::create(colored_stat_path).unwrap(), &STATS);
    }
}

#[cfg(not(feature = "stats"))]
fn export_json(thesy: &TheSy::thesy::thesy::TheSy, path: &PathBuf) {}
