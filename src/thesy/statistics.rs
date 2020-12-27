use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use egg::{Iteration, RecExpr, SymbolLang};

global_counter!(MEASURE_COUNTER, usize, usize::default());

#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "stats", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct MeasureData {
    pub start: SystemTime,
    pub amount: usize,
}

#[derive(Clone)]
#[cfg_attr(feature = "stats", derive(serde::Serialize))]
pub struct Stats {
    /// Successful conjecture proofs and their runtime.
    pub conjectures_proved: Vec<(String, String, Duration)>,
    /// Attempts to prove conjectures which failed and their runtime
    pub failed_proofs: Vec<(String, String, Duration)>,
    /// Same as prev but for given goals
    pub goals_proved: Vec<(String, String, Duration)>,
    /// Same as prev but for given goals
    pub failed_proofs_goals: Vec<(String, String, Duration)>,
    /// The iteration stats from egg foreach equivalence reduction done.
    pub equiv_red_iterations: Vec<Vec<Iteration<()>>>,
    /// Number of initial splitters and total time to complete case splitting. Not including prover.
    pub case_split: Vec<(usize, Duration)>,
    /// Amount of nodes added to graph and time it took during term deepening
    pub term_creation: Vec<(usize, Duration)>,
    /// Time to collect conjectures
    pub get_conjectures: Vec<Duration>,
    /// Lemmas proved and later were found to be unnecessary
    pub filtered_lemmas: Vec<(String, String)>,
    /// total runtime of run fn
    pub total_time: Duration,
    /// Measures to use for each run. Should be removed after used
    pub(crate) measures: HashMap<usize, MeasureData>,
    /// Run start time
    start_total: SystemTime,
}

impl Stats {
    // TODO: Create key
    pub fn init_measure(&mut self, amount: impl Fn() -> usize) -> usize {
        let mut key = 0;
        if cfg!(feature = "stats") {
            let data = MeasureData {
                start: SystemTime::now(),
                amount: amount(),
            };
            key = MEASURE_COUNTER.inc_cloning();
            self.measures.insert(key, data);
        }
        key
    }

    pub fn init_run(&mut self) {
        if cfg!(feature = "stats") {
            self.start_total = Self::get_time().unwrap();
        }
    }

    pub fn update_proved(&mut self, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.conjectures_proved.push((ex1.pretty(500), ex2.pretty(500), SystemTime::now().duration_since(data.start).unwrap()));
        }
    }

    pub fn update_filtered_conjecture(&mut self, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) {
        if cfg!(feature = "stats") {
            self.filtered_lemmas.push((ex1.pretty(500), ex2.pretty(500)));
        }
    }

    pub fn update_failed_proof(&mut self, ex1: RecExpr<SymbolLang>, ex2: RecExpr<SymbolLang>, key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.failed_proofs.push((ex1.pretty(500), ex2.pretty(500), SystemTime::now().duration_since(data.start).unwrap()));
        }
    }

    pub fn update_total(&mut self) {
        if cfg!(feature = "stats") {
            self.total_time = SystemTime::now().duration_since(self.start_total).unwrap();
        }
    }

    pub fn update_term_creation(&mut self, key: usize, n_nodes: usize) {
        if cfg!(feature = "stats") {
            let data = self.measures.remove(&key);
            self.term_creation.push((n_nodes - data.as_ref().unwrap().amount,
                                         SystemTime::now().duration_since(data.unwrap().start).unwrap()));
        }
    }

    pub fn update_rewrite_iters(&mut self, iterations: Vec<Iteration<()>>) {
        if cfg!(feature = "stats") {
            self.equiv_red_iterations.push(iterations);
        }
    }

    pub fn update_conjectures(&mut self, measure_key: usize) {
        if cfg!(feature = "stats") {
            let data = self.measures.remove(&measure_key);
            self.get_conjectures.push(SystemTime::now().duration_since(data.unwrap().start).unwrap());
        }
    }

    pub fn update_splits(&mut self, measure_key: usize) {
        if cfg!(feature = "stats") {
            let data = self.measures.remove(&measure_key);
            self.case_split.push((data.as_ref().unwrap().amount, SystemTime::now().duration_since(data.unwrap().start).unwrap()));
        }
    }
}


// Static Functions
impl Stats {
    pub fn get_time() -> Option<SystemTime> {
        if cfg!(feature = "stats") {
            Some(SystemTime::now())
        } else { None }
    }
}

impl Default for Stats {
    fn default() -> Self {
        Stats {
            conjectures_proved: Default::default(),
            failed_proofs: Default::default(),
            goals_proved: Default::default(),
            failed_proofs_goals: Default::default(),
            equiv_red_iterations: Default::default(),
            case_split: Default::default(),
            term_creation:  Default::default(),
            get_conjectures: Default::default(),
            filtered_lemmas: Default::default(),
            total_time: Default::default(),
            measures: Default::default(),
            start_total: SystemTime::now(),
        }
    }
}