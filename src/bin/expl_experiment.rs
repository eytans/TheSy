use std::alloc;
use std::any::Any;
use std::fs::File;
use std::path::PathBuf;
use std::process::exit;
use std::time::SystemTime;
use cap::Cap;
use egg::{RecExpr, SymbolLang};
use log::{LevelFilter, warn, info};
use simplelog::{ColorChoice, CombinedLogger, Config, ConfigBuilder, TerminalMode, TermLogger, WriteLogger};
use structopt::StructOpt;
use TheSy::thesy::semantics::Definitions;
use TheSy::{CaseSplitConfig, thesy, TheSyConfig};
use TheSy::SubCmd::CheckEquiv;
use TheSy::thesy::prover;
use TheSy::thesy::prover::RewriteProver;
use TheSy::thesy::statistics::{sample_graph_stats, StatsReport};

#[global_allocator]
pub(crate) static ALLOCATOR: Cap<alloc::System> = Cap::new(alloc::System, usize::MAX);

/// Arguments to use to run thesy
#[derive(StructOpt, Debug)]
struct CliOpt {
    /// The path to the file to read
    #[structopt(parse(from_os_str))]
    path: PathBuf,
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
    /// Whether to turn off invariants checking
    #[structopt(name = "disable invariants", long = "no_invariants")]
    no_invariants: bool,
}

fn main() {
    main_with_args(CliOpt::from_args())
}

fn main_with_args(args: CliOpt) {
    let log_path = args.path.with_extension("log");
    let thesy_config: simplelog::Config = ConfigBuilder::new()
        .add_filter_ignore_str("egg")
        .build();
    let egg_config: simplelog::Config = ConfigBuilder::new()
        .add_filter_allow_str("egg")
        .build();
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

    if args.no_invariants {
        warn!("Invariants checking is disabled");
        invariants::set_max_level(invariants::AssertLevel::Off);
    }


    let start = SystemTime::now();
    warn!("CLI Options: {:#?}", args);
    // Verify path from args is valid and has a th extension
    let (path, additional_terms, config) = collect_definitions_and_config(args);
    // Create thesy and update prover to my needs
    let mut thesy = update_provers_and_run(config, additional_terms);
    warn!("Finished trying proving all goals in {:?}", start.elapsed().unwrap());
    #[cfg(all(feature = "stats"))]
    sample_graph_stats(&thesy.egraph, StatsReport::End);
    if cfg!(feature = "stats") {
        thesy.finalize_stats(None);
        thesy.stats.update_mem(&ALLOCATOR);
        thesy::statistics::export_json(&mut thesy, &path);
    }
    exit(0);
}

fn collect_definitions_and_config(args: CliOpt) -> (PathBuf, Vec<RecExpr<SymbolLang>>, TheSyConfig) {
    let path = args.path;
    if !path.exists() {
        panic!("Path does not exist");
    }
    if path.extension().unwrap() != "th" {
        panic!("Path does not have a .th extension");
    }
    let defs = Definitions::from_file(&path);
    // Verify we have additional terms under the same name as the file but with a .at extension
    // So bool.th will have bool.at
    let additional_terms_path = path.with_extension("at");
    if !additional_terms_path.exists() {
        panic!("Additional terms file does not exist");
    }
    // Load additional terms as a line seperated list (filter empty) of terms in sexp format
    let additional_terms_string = std::fs::read_to_string(additional_terms_path).expect("Failed to load additional terms");
    let additional_terms: Vec<RecExpr<SymbolLang>> = additional_terms_string.lines()
        .filter(|s| !s.trim().is_empty())
        .map(|s| s.parse().unwrap()).collect();
    // Create thesy but use an updated prover
    let config = TheSyConfig::new(
        defs,
        // Should be irrelevant
        2,
        vec![],
        path.with_extension("res.th"),
        CheckEquiv,
        args.run_depth.unwrap_or(thesy::thesy::ITERN),
        CaseSplitConfig::new(
            args.case_split_depth.unwrap_or(thesy::thesy::EXP_SPLIT_D),
            args.case_split_itern.unwrap_or(thesy::thesy::EXP_SPLIT_ITERN),
        ),
        args.prover_run_depth.unwrap_or(prover::RUN_DEPTH),
        CaseSplitConfig::new(
            args.prover_split_depth.unwrap_or(prover::CASE_SPLIT_DEPTH),
            args.prover_split_itern.unwrap_or(prover::CASE_ITERN),
        ),
    );
    (path, additional_terms, config)
}

fn update_provers_and_run(mut config: TheSyConfig, additional_terms: Vec<RecExpr<SymbolLang>>) -> thesy::TheSy {
    let (mut thesy, mut case_split, mut rules) = config.create_thesy();
    thesy.update_provers(|p| {
        let casted: &RewriteProver = unsafe { &*(&p as *const dyn Any as *const RewriteProver) };
        casted.with_terms_to_push(additional_terms.clone())
    });
    // run case split mode only
    let _res = thesy.check_goals(&mut Some(&mut case_split), &mut rules);
    let _success = if !thesy.remaining_goals().unwrap().is_empty() {
        info!("Failed to prove conjectures");
        false
    } else {
        true
    };
    thesy
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::fs::File;
    use std::io::Write;

    fn test_file(filename: &str, additional_terms: &str) {
        let path = PathBuf::from(format!("tests/{}", filename));
        let mut additional_terms_path = path.clone();
        additional_terms_path.set_extension("at");
        let mut file = File::create(additional_terms_path).unwrap();
        file.write_all(additional_terms.as_bytes()).unwrap();
        let args = CliOpt {
            path,
            mem_limit: None,
            case_split_depth: None,
            case_split_itern: None,
            run_depth: None,
            prover_run_depth: None,
            prover_split_depth: None,
            prover_split_itern: None,
            no_invariants: true,
        };
        let (_, additional_terms, config) = collect_definitions_and_config(args);
        let thesy = update_provers_and_run(config, additional_terms);
        assert!(thesy.remaining_goals().unwrap().is_empty());
    }

    #[test]
    fn test_expl_test() {
        init_logging();

        test_file("expl_test.th", "vac");
    }

    fn init_logging() {
        let log_path = "test.log";
        let thesy_config: simplelog::Config = ConfigBuilder::new()
            .add_filter_ignore_str("egg")
            .build();
        let egg_config: simplelog::Config = ConfigBuilder::new()
            .add_filter_allow_str("egg")
            .build();
        CombinedLogger::init(
            vec![
                TermLogger::new(LevelFilter::Debug, thesy_config, TerminalMode::Mixed, ColorChoice::Auto),
                TermLogger::new(LevelFilter::Warn, egg_config, TerminalMode::Mixed, ColorChoice::Auto),
                WriteLogger::new(LevelFilter::Info, Config::default(), File::create(log_path).unwrap()),
            ]
        ).unwrap();
    }
}