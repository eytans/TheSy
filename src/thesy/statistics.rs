use egg::{RecExpr, Pattern, SymbolLang, Iteration, IterationData};
use std::time::Duration;


#[derive(Clone, Default)]
#[cfg_attr(feature = "stats", derive(serde::Serialize))]
pub struct Stats {
    /// Successful conjecture proofs and their runtime.
    pub conjectures_proved: Vec<(String, String, Duration)>,
    /// Attempts to prove conjectures which failed and their runtime
    pub failed_proofs: Vec<(String, String, Duration)>,
    /// Same as prev but for given goals
    pub goals_proved: Vec<(String, String, Duration)>,
    /// Same as prev but for given goals
    pub failed_proofs_lemmas: Vec<(String, String, Duration)>,
    /// The iteration stats from egg foreach equivalence reduction done.
    pub equiv_red_iterations: Vec<Vec<Iteration<()>>>,
    /// Number of initial splitters and total time to complete case splitting. Not including prover.
    pub case_split: Vec<(usize, Duration)>,
    /// Amount of nodes added to graph and time it took during term deepening
    pub term_creation: Vec<(usize, Duration)>,
    /// Time to collect conjectures
    pub get_conjectures: Vec<Duration>,
    /// Lemmas proved and later were found to be unnecessary
    pub filtered_lemmas: Vec<(String, String)>
}