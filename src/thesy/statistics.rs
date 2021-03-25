use std::collections::HashMap;
use std::time::{Duration, SystemTime};

use egg::{Iteration, RecExpr, SymbolLang, IterationData, EGraph, Language, Analysis};

global_counter!(MEASURE_COUNTER, usize, usize::default());

#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "stats", derive(serde::Serialize, serde::Deserialize))]
pub(crate) struct MeasureData {
    pub start: SystemTime,
    pub amount: usize,
}

#[derive(Clone)]
pub struct GraphData {
    pub classes: usize,
    pub nodes: usize,
}

impl GraphData {
    pub fn new<L: Language, N: Analysis<L>>(graph: &EGraph<L, N>) -> GraphData {
        GraphData { classes: graph.number_of_classes(), nodes: graph.total_number_of_nodes() }
    }
}

#[derive(Clone)]
pub struct CaseSplitData {
    pub graph_before: GraphData,
    pub graph_after: GraphData,
    pub iterations: Vec<Iteration<()>>,
    pub duration: Duration,
    /// Splitter reconstructed and relevant collected data
    pub inner_splits: Vec<(String, Vec<CaseSplitData>)>,
    start: SystemTime,
}

impl CaseSplitData {
    pub fn new<L: Language, N: Analysis<L>>(graph: &EGraph<L, N>) -> CaseSplitData {
        CaseSplitData {
            start: SystemTime::now(),
            graph_before: GraphData::new(graph),
            graph_after: GraphData { nodes: 0, classes: 0 },
            iterations: vec![],
            duration: Duration::default(),
            inner_splits: vec![],
        }
    }

    pub fn finalizer<L: Language, N: Analysis<L>>(&mut self, graph: &EGraph<L, N>) {
        self.graph_after = GraphData::new(graph);
        self.duration = self.start.elapsed().unwrap();
    }
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
    pub case_split: Vec<CaseSplitData>,
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

    pub fn update_proved(&mut self,
                         ex1: &RecExpr<SymbolLang>,
                         ex2: &RecExpr<SymbolLang>,
                         key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.conjectures_proved.push(Self::pretty_with_time(ex1, ex2, data.start));
        }
    }

    pub fn update_filtered_conjecture(&mut self,
                                      ex1: &RecExpr<SymbolLang>,
                                      ex2: &RecExpr<SymbolLang>) {
        if cfg!(feature = "stats") {
            self.filtered_lemmas.push((ex1.pretty(500), ex2.pretty(500)));
        }
    }

    pub fn update_failed_proof(&mut self,
                               ex1: RecExpr<SymbolLang>,
                               ex2: RecExpr<SymbolLang>,
                               key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.failed_proofs.push(Self::pretty_with_time(&ex1, &ex2, data.start));
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
            self.term_creation.push((
                n_nodes - data.as_ref().unwrap().amount,
                Self::duration(data.unwrap().start)));
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
            self.get_conjectures.push(Self::duration(data.unwrap().start));
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

    fn pretty_with_time(ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, start: SystemTime)
                        -> (String, String, Duration) {
        (ex1.pretty(500), ex2.pretty(500), Self::duration(start))
    }

    fn duration(start: SystemTime) -> Duration {
        SystemTime::now().duration_since(start).unwrap()
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
            term_creation: Default::default(),
            get_conjectures: Default::default(),
            filtered_lemmas: Default::default(),
            total_time: Default::default(),
            measures: Default::default(),
            start_total: SystemTime::now(),
        }
    }
}