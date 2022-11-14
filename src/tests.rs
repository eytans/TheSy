use crate::thesy::{semantics, TheSy};
use egg::{RecExpr, SymbolLang, Id, Rewrite};
use crate::thesy::semantics::Definitions;
use crate::thesy::case_split::CaseSplit;
use crate::thesy::prover::Prover;
use std::fs::File;
use std::ops::Not;
use thesy_parser::ast;
use std::str::FromStr;
use std::sync::atomic::AtomicBool;
use std::sync::Mutex;
use indexmap::IndexSet;
use thesy_parser::ast::{Expression, Terminal};
use egg::reconstruct::reconstruct;
use crate::{tests, TheSyConfig};
use crate::lang::ThExpr;

lazy_static!(
    static ref log_initialized: Mutex<bool> = Mutex::new(false);
);
pub fn init_logging() {
    use simplelog::*;

    let mut lock = log_initialized.lock().unwrap();
    if lock.not() {
        let mut thesy_config: simplelog::Config = ConfigBuilder::new().add_filter_ignore_str("egg").build();
        let mut egg_config: simplelog::Config = ConfigBuilder::new().add_filter_allow_str("egg").build();
        let logger = CombinedLogger::init(
            vec![
                TermLogger::new(LevelFilter::Debug, thesy_config, TerminalMode::Mixed, ColorChoice::Auto),
                TermLogger::new(LevelFilter::Warn, egg_config, TerminalMode::Mixed, ColorChoice::Auto),
                WriteLogger::new(LevelFilter::Info, Config::default(), File::create("my_rust_bin.log").unwrap()),
            ]
        );
        if logger.is_err() {
            println!("Error initializing log: {}", logger.unwrap_err());
        }
        *lock = true;
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProofMode {
    /// Proved by case split without exploration
    CaseSplit,
    /// Proved by applying the prover directly to the terms
    Prover,
    /// Terms were not created by increase depth
    TermNotCreated,
    /// Examples were not merged over given terms
    ExamplesFailed,
    /// Proof failed
    Failed,
}

// TODO: maybe hint on recursion
pub fn test_terms(mut definitions: Definitions) -> ProofMode {
    let mut thesy: TheSy = TheSy::from(&definitions);
    let mut case_splitter = TheSy::create_case_splitter(definitions.case_splitters.clone());
    warn!("Case splitters: {:?}", &case_splitter);
    let mut rws = thesy.system_rws.clone();
    rws.extend_from_slice(&definitions.rws);
    assert_eq!(1, definitions.goals.len());
    assert_eq!(1, definitions.conjectures.len());
    let (vars, holes, precond, ex1, ex2) = definitions.conjectures.first().unwrap();
    let (mut ast_precond, mut ast_exp1, mut ast_exp2) = definitions.goals.clone().pop().unwrap();

    // Assert terms are not equal
    assert!(!TheSy::check_equality(&rws, precond, ex1, ex2));

    // let ph_precond = ast_precond.map(|e| e.map(exp_translator));
    let ph_exp1 = translate_expression(&mut ast_exp1);
    let ph_exp2 = translate_expression(&mut ast_exp2);

    // Create term succeeds
    thesy.increase_depth();
    thesy.equiv_reduc(&mut rws);
    thesy.increase_depth();

    let classes = thesy.egraph.classes().map(|x| x.id).collect::<IndexSet<Id>>();
    let ph_id1 = thesy.egraph.add_expr(&ph_exp1);
    let ph_id2 = thesy.egraph.add_expr(&ph_exp2);
    info!("ph_exp1: {}, ph_exp2: {}", ph_exp1, ph_exp2);

    if !classes.contains(&thesy.egraph.find(ph_id1)) ||
        !classes.contains(&thesy.egraph.find(ph_id2)) {
        return ProofMode::TermNotCreated;
    }

    let mut egraph = Prover::create_graph(precond.as_ref(), &ex1, &ex2);

    // Attempt prove by case split
    case_splitter.case_split(&mut egraph, 3, &rws, 12);
    if egraph.add_expr(ex1) == egraph.add_expr(ex2) {
        return ProofMode::CaseSplit;
    }


    // Reduce finds equality on examples
    thesy.equiv_reduc(&mut rws);
    case_splitter.case_split(&mut thesy.egraph, 2, &rws, 8);
    let ph_id1 = thesy.egraph.find(ph_id1);
    let ph_id2 = thesy.egraph.find(ph_id2);
    if precond.is_none() && thesy.datatypes.keys().all(|d| {
        thesy.get_example_ids(d, ph_id1)
            != thesy.get_example_ids(d, ph_id2)
    }) {
        println!("ph1: {}", reconstruct(&thesy.egraph, ph_id1, 5)
            .map_or("".to_string(), |x| x.pretty(500)));
        println!("ph2: {}", reconstruct(&thesy.egraph, ph_id2, 5)
            .map_or("".to_string(), |x| x.pretty(500)));
        return ProofMode::ExamplesFailed;
    }


    test_prover(&definitions)[0]
}

fn translate_expression(ast_exp1: &mut Expression) -> ThExpr {
    RecExpr::from_str(&*ast_exp1.map(&mut |t| terminal_ph_translator(t)).to_sexp_string()).unwrap()
}

fn terminal_ph_translator(t: &Terminal) -> Terminal {
    if let Some(a) = t.anno() {
        Terminal::Id(
            TheSy::get_ph(&RecExpr::from_str(
                &*a.get_type().unwrap().to_sexp_string()
            ).unwrap(),
                          a.get_ph().unwrap(),
            ).name, Some(a.clone()))
    } else {
        t.clone()
    }
}


pub fn test_prover(definitions: &Definitions) -> Vec<ProofMode> {
    let mut thesy: TheSy = TheSy::from(definitions);
    let mut case_splitter = TheSy::create_case_splitter(definitions.case_splitters.clone());
    warn!("Case splitters: {:?}", &case_splitter);
    let mut rws = thesy.system_rws.clone();
    rws.extend_from_slice(&definitions.rws);

    let mut res = Vec::new();
    for (c, g) in definitions.conjectures.iter().zip(definitions.goals.iter()) {
        let (vars, holes, precond, ex1, ex2) = c;
        let (mut ast_precond, mut ast_exp1, mut ast_exp2) = g.clone();
        // let ph_precond = ast_precond.map(|e| e.map(exp_translator));
        let ph_exp1 = translate_expression(&mut ast_exp1);
        let ph_exp2 = translate_expression(&mut ast_exp2);

        let mut proof_res = None;
        for d in &definitions.datatypes {
            // Check exploration results

            // Attempt proof
            let prover = &thesy.datatypes[d];
            warn!("Proving goal with {}", d);
            let temp = prover.prove_all_split_d(&mut Some(&mut case_splitter),
                                               &rws,
                                               Option::from(precond),
                                               &ph_exp1,
                                               &ph_exp2,
                                               1);
            if temp.is_some() {
                proof_res = Some(ProofMode::Prover);
                break;
            }
        }
        if proof_res.is_none() {
            proof_res = Some(ProofMode::Failed);
        }
        res.push(proof_res.unwrap());
    }
    res
}
