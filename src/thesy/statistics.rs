use egg::{RecExpr, Pattern, SymbolLang, Iteration, IterationData};
use std::time::Duration;

#[derive(Clone, Default)]
struct Stats {
    pub conjectures_proved: Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Duration)>,
    pub failed_proofs: Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Duration)>,
    pub equiv_red_iterations: Vec<Vec<Iteration<()>>>,
    pub case_split: Vec<(usize, Duration)>,
    pub term_creation: Vec<(usize, Duration)>,
    pub get_conjectures: Vec<Duration>
}