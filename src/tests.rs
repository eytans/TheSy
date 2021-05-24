use crate::thesy::TheSy;
use egg::{RecExpr, SymbolLang, Id};
use crate::thesy::semantics::Definitions;
use crate::thesy::case_split::CaseSplit;
use crate::thesy::prover::Prover;
use std::collections::HashSet;

pub fn init_logging() {
    use simplelog::*;

    let mut builder = ConfigBuilder::new();
    builder.add_filter_ignore("egg".parse().unwrap());
    let config = builder.build();
    TermLogger::init(LevelFilter::Info, config, TerminalMode::Mixed).unwrap();
}

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
    let mut case_splitter = TheSy::create_case_splitter(definitions.case_splitters);
    assert_eq!(1, definitions.conjectures.len());
    let (vars, precond, ex1, ex2) =
        definitions.conjectures.first().unwrap();

    // Assert terms are not equal
    assert!(!TheSy::check_equality(&definitions.rws, precond, ex1, ex2));

    let mut egraph = Prover::create_graph(precond.as_ref(), &ex1, &ex2);

    // Attempt prove by case split
    case_splitter.case_split(&mut egraph, 1, &definitions.rws, 8);
    if egraph.add_expr(ex1) == egraph.add_expr(ex2) {
        return ProofMode::CaseSplit;
    }

    // TODO: override expression 1 and 2 into ph format.

    // Create term succeeds
    thesy.increase_depth();
    thesy.equiv_reduc(&mut definitions.rws);
    thesy.increase_depth();
    let classes = thesy.egraph.classes().map(|x| x.id).collect::<HashSet<Id>>();
    if (!classes.contains(&thesy.egraph.add_expr(ex1))) ||
        !classes.contains(&thesy.egraph.add_expr(ex2)) {
        return ProofMode::TermNotCreated;
    }

    for d in &definitions.datatypes {
        // Check exploration results
        thesy.equiv_reduc(&mut definitions.rws);
        // TODO: generalize ex1\ex2 to placeholders
        // TODO: verify both are equal over examples (for at least one permutation of ph assignment.
        // if  {
        //
        // }

        // Attempt proof
        let prover = &thesy.datatypes[d];
        let res = prover.prove_ind(&mut Some(&mut case_splitter), &definitions.rws, ex1, ex2);
        if res.is_some() {
            return ProofMode::Prover;
        }
    }

    return ProofMode::Failed;
}