use std::alloc::GlobalAlloc;
use std::fs::File;
use std::path::PathBuf;
use std::time::{Duration, SystemTime};

use cap::Cap;
#[allow(unused_imports)]
use egg::{ColorId, Iteration};
use indexmap::{IndexMap, IndexSet};
use serde::{Deserialize, Serialize};
use crate::lang::{Function, ThEGraph, ThExpr};
use crate::{PRETTY_W, thesy, ALLOCATOR};
use crate::thesy::case_split::CaseSplitStats;

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
    pub(crate) measures: IndexMap<usize, MeasureData>,
    /// Run start time
    start_total: SystemTime,
    /// Total amount of memory allocated
    pub total_allocated: usize,
    /// Max amount of memory allocated
    pub max_allocated: usize,
    /// Case split stats
    pub case_split_stats: CaseSplitStats,
    /// Iteration of check_equiv reductions
    pub equality_check_iterations: Vec<Vec<Iteration<()>>>,
    /// Total search time - milliseconds
    pub total_search_time: Option<f64>,
    /// Total apply time - milliseconds
    pub total_apply_time: Option<f64>,
    /// Total rebuild time - milliseconds
    pub total_rebuild_time: Option<f64>,
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

    pub fn update_proved(&mut self, ex1: &ThExpr, ex2: &ThExpr, key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.conjectures_proved.push((ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W),
                                          SystemTime::now().duration_since(data.start).unwrap()));
        }
    }

    pub fn update_filtered_conjecture(&mut self, ex1: &ThExpr, ex2: &ThExpr) {
        if cfg!(feature = "stats") {
            self.filtered_lemmas.push((ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W)));
        }
    }

    pub fn update_failed_proof(&mut self, ex1: ThExpr, ex2: ThExpr, key: usize) {
        if cfg!(feature = "stats") {
            let data = &self.measures[&key];
            self.failed_proofs.push((ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W),
                                     SystemTime::now().duration_since(data.start).unwrap()));
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

    pub fn update_mem<T>(&mut self, cap: &cap::Cap<T>) {
        if cfg!(feature = "stats") {
            self.total_allocated = cap.total_allocated();
            self.max_allocated = cap.max_allocated();
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
            total_allocated: Default::default(),
            max_allocated: Default::default(),
            case_split_stats: Default::default(),
            equality_check_iterations: Default::default(),
            total_search_time: Default::default(),
            total_apply_time: Default::default(),
            total_rebuild_time: Default::default(),
        }
    }
}

#[cfg(feature = "stats")]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GraphStats {
    #[cfg(any(feature = "split_no_cremove", feature = "split_no_cmemo"))]
    pub should_delete: IndexMap<ColorId, usize>,
    #[cfg(feature = "split_colored")]
    pub colors_sizes: IndexMap<ColorId, usize>,
    pub black_size: usize,
    #[cfg(feature = "split_colored")]
    pub vacuos_colors: Vec<ColorId>,
    #[cfg(feature = "keep_splits")]
    pub split_sizes: Vec<usize>,
    pub graph_memory: usize,
}

#[cfg(all(feature = "stats", feature = "keep_splits"))]
fn get_split_sizes(egraph: &ThEGraph) -> Vec<usize> {
    let res: Vec<usize> = egraph.all_splits.iter()
    .flat_map(|g| {
        let mut res = get_split_sizes(g);
        res.insert(0, g.total_size());
        res
    }).collect();
    res
}

impl GraphStats {
    /**
     * Returns the memory used by the egraph. Calculate by using Archimedas.
     * First turn off cap stats, then get the total allocated memory, 
     * clone graph, get total again, then turn on cap stats again.
     */
    pub fn memory_used(egraph: &ThEGraph, cap: &mut Cap<impl GlobalAlloc>) -> usize {
        let mut current = cap.allocated();
        cap.disable_stats();
        {
            let g = egraph.clone();
            current = cap.allocated() - current;
            println!("Prevent drop - egraph size: {}", g.total_size());
        }
        cap.enable_stats();
        current
    }
    
    pub fn from_egraph(egraph: &ThEGraph) -> Self {
        let mut black_enodes = IndexSet::new();
        let mut colored_enodes = egraph.colors().map(|c| (c.get_id(), IndexSet::new())).collect::<IndexMap<_, _>>();
        if cfg!(feature = "split_no_cremove") || cfg!(feature = "split_no_cmemo") {
            for class in egraph.classes() {
                if let Some(color) = class.color() {
                    let set = colored_enodes.get_mut(&color).unwrap();
                    class.nodes.iter().map(|n| egraph.colored_canonize(color, n)).for_each(|n| {
                        set.insert(n);
                    });
                } else {
                    black_enodes.extend(class.nodes.iter().cloned());
                }
            }
            for c in egraph.colors() {
                let fixed_black = black_enodes.iter().map(|n| egraph.colored_canonize(c.get_id(), n)).collect::<IndexSet<_>>();
                colored_enodes.get_mut(&c.get_id()).unwrap().retain(|n| fixed_black.contains(n));
            }
        }
        let memory_used = unsafe { Self::memory_used(egraph, &mut ALLOCATOR) };
        GraphStats {
            #[cfg(any(feature = "split_no_cremove", feature = "split_no_cmemo"))]
            should_delete: colored_enodes.iter().map(|(k, v)| (*k, v.len())).collect(),
            #[cfg(feature = "split_colored")]
            colors_sizes: egraph.color_sizes().collect(),
            black_size: egraph.total_size(),
            #[cfg(feature = "split_colored")]
            vacuos_colors: egraph.detect_color_vacuity(),
            #[cfg(feature = "keep_splits")]
            split_sizes: get_split_sizes(egraph),
            graph_memory: memory_used,
        }
    }
}

impl From<&ThEGraph> for GraphStats {
    fn from(graph: &ThEGraph) -> Self {
        GraphStats::from_egraph(graph)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StatsReport {
  ThesyDepth(usize),
  CaseSplitDepth(usize),
  ProverBaseEnd(Function, ThExpr, ThExpr),
  ProverIndEnd(Function, ThExpr, ThExpr),
  UNKNOWN,
  End,
}

pub static mut STATS: Vec<(StatsReport, GraphStats)> = vec![];

pub fn sample_graph_stats(egraph: &ThEGraph, report: StatsReport) {
    unsafe {
        STATS.push((report, GraphStats::from(egraph)));
    }
}


#[cfg(feature = "stats")]
pub fn export_json(thesy: &mut thesy::TheSy, path: &PathBuf) {
    let stat_path = path.with_extension("stats.json");
    let colored_stat_path = path.with_extension("colored_stats.json");
    thesy.finalize_stats(None);
    serde_json::to_writer(File::create(stat_path).unwrap(), &thesy.stats).unwrap();
    unsafe {
        serde_json::to_writer(File::create(colored_stat_path).unwrap(), &STATS).unwrap();
    }
}

#[cfg(not(feature = "stats"))]
fn export_json(thesy: &TheSy::thesy::thesy::TheSy, path: &PathBuf) {}


#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use crate::tests::init_logging;
    #[allow(unused_imports)]
    use crate::thesy::statistics::STATS;
    #[allow(unused_imports)]
    use crate::thesy::TheSy;

    #[cfg(all(feature = "stats", feature = "keep_splits"))]
    #[test]
    fn test_get_split_sizes() {
        use crate::thesy::statistics::get_split_sizes;

        init_logging();

        // Create a new egraphs with sizes 0-4
        let mut egraphs = vec![];
        let mut base = crate::lang::ThEGraph::new(());
        egraphs.push(base.clone());
        for i in 0..4 {
            base.add_expr(&i.to_string().parse().unwrap());
            egraphs.push(base.clone());
        }
        assert_eq!(egraphs[4].total_size(), 4);
        let res = get_split_sizes(&base);
        assert_eq!(res.len(), 0);
        let mut egraph4 = egraphs.remove(4);
        let egraph3 = egraphs.remove(3);
        let egraph2 = egraphs.remove(2);
        let egraph1 = egraphs.remove(1);
        egraph4.all_splits.push(egraph3);
        egraphs[0].all_splits.push(egraph4);
        let res = get_split_sizes(&egraphs[0]);
        assert_eq!(res.len(), 2);
        assert_eq!(res[0], 4);
        assert_eq!(res[1], 3);
        egraphs[0].all_splits[0].all_splits.push(egraph2);
        let res = get_split_sizes(&egraphs[0]);
        assert_eq!(res.len(), 3);
        assert_eq!(res[0], 4);
        assert_eq!(res[1], 3);
        assert_eq!(res[2], 2);
        egraphs[0].all_splits.push(egraph1);
        let res = get_split_sizes(&egraphs[0]);
        assert_eq!(res.len(), 4);
        assert_eq!(res[0], 4);
        assert_eq!(res[1], 3);
        assert_eq!(res[2], 2);
        assert_eq!(res[3], 1);
    }

    #[cfg(feature = "stats")]
    #[test]
    fn test_collecting_stats() {
        use crate::thesy::prover::Prover;

        init_logging();

        // Do a simple thesy run
        let (thesy, _rws) = crate::TheSyConfig::from_path("tests/filter.th".to_string()).run(Some(2));
        // Assert we have case split iterations
        assert!(thesy.stats.case_split_stats.iterations.iter().any(|v|
            v.len() > 0 && v.iter().any(|v| v.rebuild_time > 0.0)));
        // Assert we have prover iterations
        assert!(thesy.datatypes.values().any(|p| p.get_stats().iterations.iter().any(|v|
            v.len() > 0 && v.iter().any(|v| v.search_time > 0.0))));
        // Assert we have thesy iterations
        assert!(thesy.stats.equiv_red_iterations.iter().any(|v|
            v.len() > 0 && v.iter().any(|v| v.apply_time > 0.0)));
        // Assert we have thesy::equiv_check iterations
        assert!(thesy.stats.equality_check_iterations.iter().any(|v|
            v.len() > 0 && v.iter().any(|v| v.apply_time > 0.0)));
    }

    #[test]
    fn test_collecting_split_sizes() {
        use crate::TheSyConfig;

        init_logging();

        // Do a simple thesy run
        let _ = TheSyConfig::from_path("tests/minus.th".to_string()).run(Some(1));
        // get statistics
        unsafe {
            #[cfg(all(feature = "stats", feature = "keep_splits"))]
            {
                let total_splits = STATS.iter()
                    .map(|(_, s)| {
                    println!("{:?}", s.split_sizes); 
                    s.split_sizes.len()
                }).max().unwrap();
                info!("Found {} splits statistics", total_splits);
                assert!(STATS.iter().any(|(_, stats)| stats.split_sizes.len() > 0 &&
                    stats.split_sizes.iter().any(|v| *v > 0)));
            }
            #[cfg(all(feature = "stats", feature = "split_colored"))]
            assert!(STATS.iter().any(|(_, stats)| stats.colors_sizes.len() > 0 
                && stats.colors_sizes.values().any(|v| *v > 0)));
        }
    }

    #[test]
    fn test_collecting_vacuity() {
        use crate::TheSyConfig;

        init_logging();

        // Do a simple thesy run
        let (thesy, _rw) = TheSyConfig::from_path("tests/vacuity.th".to_string()).run(Some(1));
        assert!(thesy.stats.case_split_stats.vacuous_cases.iter().any(|v| *v > 0));
        #[cfg(feature = "split_colored")]
        unsafe {
            assert!(STATS.iter().any(|x| x.1.vacuos_colors.len() > 0));
        }
    }
}