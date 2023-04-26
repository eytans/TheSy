use std::collections::hash_map::RandomState;
use std::iter;
use std::iter::FromIterator;
use std::rc::Rc;
use std::str::FromStr;
use std::time::{Duration, SystemTime};

use egg::*;
use egg::costs::{MinRep, RepOrder};
use egg::expression_ops::{IntoTree, Tree};
use egg::pretty_string::PrettyString;
use egg::searchers::MultiDiffSearcher;
use egg::tools::tools::choose;
use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use log::{info, warn};

use crate::{CaseSplitConfig, PRETTY_W, ProverConfig, utils};
use crate::lang::*;
use crate::thesy::{case_split, consts};
use crate::thesy::case_split::CaseSplit;
use crate::thesy::example_creator::Examples;
use crate::thesy::prover::{Prover, RewriteProver};
use crate::thesy::statistics::{sample_graph_stats, Stats, StatsReport};

pub const ITERN: usize = 12;
pub const EXP_SPLIT_D: usize = 2;
pub const EXP_SPLIT_ITERN: usize = 4;

/// Theory Synthesizer - Explores a given theory finding and proving new lemmas.
pub struct TheSy {
    /// known datatypes to wfo rewrites for induction
    pub(crate) datatypes: IndexMap<DataType, Box<dyn Prover + 'static>>,
    /// known function declerations and their types
    dict: Vec<Function>,
    /// egraph which is expanded as part of the exploration
    pub egraph: ThEGraph,
    /// searchers used to create the next depth of terms
    searchers: IndexMap<String, (MultiDiffSearcher<Pattern<SymbolLang>>, Vec<(Var, ThExpr)>)>,
    /// map maintaining the connection between eclasses created by sygue
    /// and their associated eclasses with `ind_ph` replaced by symbolic examples.
    example_ids: IndexMap<DataType, IndexMap<Id, Vec<Id>>>,
    /// Flattern apply rewrites are used for high order function such as fold.
    /// Ite rewrites
    /// Equality rewrite
    /// Or and And rewrites
    /// TODO: add support for partial application
    pub system_rws: Vec<ThRewrite>,
    /// Limits to use in equiv reduc
    node_limit: usize,
    /// Limits to use in equiv reduc
    iter_limit: usize,
    /// Lemmas given by user to prove. Continue exploration until all lemmas are provable then stop.
    /// If empty then TheSy will fully explore the space. (precondition, ex1, ex2)
    goals: Option<Vec<Vec<(Option<ThExpr>, ThExpr, ThExpr)>>>,
    /// If stats enable contains object collecting runtime data on thesy otherwise None.
    pub stats: Stats,
    /// Assumptions to colors
    // assumptions: BiHashMap<Vec<Id>, ColorId>,
    /// the hooks are used after every step of TheSy which could expand the rules set
    /// currently used to support parallel running
    #[allow(dead_code)]
    after_inference_hooks: Vec<Box<dyn FnMut(&mut Self, &mut Vec<ThRewrite>) -> Result<(), String>>>,
    //after_inference_hooks: Vec<Box<dyn FnMut(&mut Self, &Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, ThRewrite)>) -> Result<(), String>>>,
    /// the hooks are used before every step of TheSy which could expand the rules set
    /// currently used to support parallel running
    #[allow(dead_code)]
    before_inference_hooks: Vec<Box<dyn FnMut(&mut Self, &mut Vec<ThRewrite>) -> Result<(), String>>>,
    /// hooks passed to [runner]
    /// for more info check: [EGG] documentation
    #[allow(dead_code)]
    equiv_reduc_hooks: Vec<Box<dyn FnMut(&mut Runner<SymbolLang, ()>, &mut Vec<ThRewrite>) -> Result<(), String>>>,
    /// Vars created for examples, used to reduce case split depth
    #[allow(dead_code)]
    examples: IndexMap<DataType, Examples>,
    /// Total amount of iters
    total_iters: usize,
    /// Case split configuration
    case_split_config: CaseSplitConfig,
}

/// *** TheSy Statics ***
impl TheSy {
    #[cfg(feature = "stats")]
    pub fn get_prover_iters(&self) -> Vec<Vec<Vec<Iteration<()>>>> {
        self.datatypes.values().map(|x| x.get_stats().iterations.clone()).collect_vec()
    }

    fn replace_ops(exp: &ThExpr, replacments: &IndexMap<Symbol, Symbol>) -> ThExpr {
        RecExpr::from(exp.as_ref().iter().map(|s| replacments.get(&s.op)
            .map(|x| SymbolLang::new(x.as_str(), s.children.clone())).unwrap_or(s.clone())).collect_vec())
    }

    fn replace_op(exp: &ThExpr, orig: Symbol, replacment: Symbol) -> ThExpr {
        Self::replace_ops(exp, &IndexMap::from_iter(iter::once((orig, replacment))))
    }

    fn create_sygue_serchers<'a>(dict: &[Function], datatypes: impl Iterator<Item=&'a DataType>) -> IndexMap<String, (MultiDiffSearcher<Pattern<SymbolLang>>, Vec<(Var, ThExpr)>)> {
        let mut res = IndexMap::new();
        let datas = datatypes.cloned().collect_vec();
        TheSy::known_functions(&datas, dict).for_each(|fun| {
            if !fun.params.is_empty() {
                let params: Vec<(Var, ThExpr)> = fun.params.iter().enumerate().map(|(i, t)| {
                    (Var::from_str(&*format!("?param_{}", i)).unwrap(), t.clone())
                }).collect_vec();
                let patterns = params.iter()
                    .flat_map(|(v, typ)| {
                        vec![
                            Pattern::from_str(&*format!("(typed {} {})", v.to_string(),
                                                        typ.pretty(PRETTY_W))).unwrap(),
                        ]
                    }).collect::<Vec<Pattern<SymbolLang>>>();
                res.insert(fun.name.clone(), (MultiDiffSearcher::new(patterns), params));
            }
        });
        res
    }

    pub fn new(datatype: DataType, examples: Examples, dict: Vec<Function>) -> TheSy {
        Self::new_with_ph(
            vec![datatype.clone()],
            IndexMap::from_iter(iter::once((datatype, examples))),
            dict,
            2,
            None,
            ITERN,
            None,
            None,
        )
    }

    pub fn new_with_ph(
        datatypes: Vec<DataType>,
        examples: IndexMap<DataType, Examples>,
        dict: Vec<Function>,
        ph_count: usize,
        lemmas: Option<Vec<(IndexMap<ThExpr, ThExpr>, IndexSet<ThExpr>, Option<ThExpr>, ThExpr, ThExpr)>>,
        run_depth: usize,
        prover_config: Option<ProverConfig>,
        case_split_config: Option<CaseSplitConfig>,
    ) -> TheSy {
        debug_assert!(examples.iter().all(|(d, e)| &e.datatype == d));
        let datatype_to_prover: IndexMap<DataType, Box<dyn Prover>> = datatypes.iter()
            .map(|d| {
                let prover = prover_config.as_ref().map_or(
                        RewriteProver::new(d.clone()),
                        |x| RewriteProver::new_config(d.clone(), x.clone()));
                let boxed: Box<dyn Prover> = Box::new(prover);
                (d.clone(), boxed)
            }).collect();
        let (mut egraph, example_ids) = TheSy::create_graph_example_ids(&datatypes, &examples, &dict, ph_count);

        let apply_rws = TheSy::create_apply_rws(&dict, &datatypes, ph_count);
        let system_rws: Vec<ThRewrite> = apply_rws.into_iter()
            .chain(consts::ite_rws().into_iter())
            .chain(consts::equality_rws().into_iter())
            .chain(consts::bool_rws().into_iter())
            .chain(consts::less_rws().into_iter())
            .chain(consts::is_rws().into_iter())
            .collect_vec();

        // TODO: replace placeholders only for holes and not for all terminals (also in creating ph0)
        let conjectures = lemmas.map(|v| v.into_iter()
            .map(|(vars, holes, precond, ex1, ex2)| {
                trace!("Creating conjectures from lemma: {}{} => {}",precond.as_ref()
                    .map(|c| format!("{} |> ", c.pretty(PRETTY_W)))
                    .unwrap_or("".to_string()),ex1.pretty(PRETTY_W),ex2.pretty(PRETTY_W));
                trace!("Holes: {}", holes.iter().map(|h| h.pretty(PRETTY_W)).join(", "));
                trace!("Vars: {}", vars.iter().map(|(k, v)|
                    format!("{}: {}", k.pretty(PRETTY_W), v.pretty(PRETTY_W))).join(", "));
                let mut types_to_vars: IndexMap<ThExpr, IndexMap<Symbol, Function>> = IndexMap::new();
                for v in vars {
                    if !holes.contains(&v.0) {
                        continue;
                    }
                    if !types_to_vars.contains_key(&v.1) {
                        types_to_vars.insert(v.1.clone(), IndexMap::new());
                    }
                    let current_ph = types_to_vars[&v.1].len() + 1;
                    types_to_vars.get_mut(&v.1).unwrap().insert(v.0.as_ref().last().unwrap().op, TheSy::get_ph(&v.1, current_ph));
                }
                let replacments: IndexMap<Symbol, Symbol> = types_to_vars.values().flat_map(|v| {
                    v.iter().map(|(k, f)| (*k, Symbol::from(&f.name)))
                }).collect();
                let precond_replaced = precond.map(|p| Self::replace_ops(&p, &replacments));
                let ex1_replaced = Self::replace_ops(&ex1, &replacments);
                let ex2_replaced = Self::replace_ops(&ex2, &replacments);
                types_to_vars.keys().filter(|key| datatypes.iter()
                    .any(|d| d.as_exp().into_tree() == key.into_tree()))
                    .flat_map(|typ| {
                        types_to_vars[typ].values().zip(iter::once(typ).cycle()).map(|(ph, typ)| {
                            (precond_replaced.clone().map(|p| Self::replace_op(&p, Symbol::from(&ph.name), Symbol::from(&Self::get_ph(typ, 0).name))),
                             Self::replace_op(&ex1_replaced, Symbol::from(&ph.name), Symbol::from(&Self::get_ph(typ, 0).name)),
                             Self::replace_op(&ex2_replaced, Symbol::from(&ph.name), Symbol::from(&Self::get_ph(typ, 0).name)))
                        })
                    }).collect_vec()
            }).collect_vec());

        let stats = Default::default();
        let searchers = Self::create_sygue_serchers(&dict, datatypes.iter());

        warn!("Proof mode: {}", conjectures.is_some());

        let op_ids = datatypes.iter().map(|d| {
            d.constructors.iter().map(|c| {
                SymbolLang::leaf(c.name.clone()).op_id()
            }).collect_vec()
        }).collect_vec();
        egraph.vacuity_ops = op_ids;

        TheSy {
            datatypes: datatype_to_prover,
            dict,
            egraph,
            searchers,
            example_ids,
            system_rws,
            node_limit: 400000,
            iter_limit: run_depth,
            goals: conjectures,
            stats,
            // assumptions: Default::default(),
            before_inference_hooks: Default::default(),
            after_inference_hooks: Default::default(),
            equiv_reduc_hooks: Default::default(),
            examples,
            total_iters: 0,
            case_split_config: case_split_config.unwrap_or(CaseSplitConfig::new(2, 4)),
        }
    }

    pub fn update_provers(&mut self, mut f: impl FnMut(Box<dyn Prover + 'static>) -> Box<dyn Prover + 'static>) {
        self.datatypes = std::mem::take(&mut self.datatypes)
            .into_iter().map(|(k, v)| (k, f(v))).collect();
    }

    pub fn get_example_ids(&self, datatype: &DataType, class: Id) -> Option<Vec<Id>> {
        self.example_ids.get(datatype).map(|x| x.get(&class).map(|v| v.iter().map(|c| self.egraph.find(*c)).collect_vec())).unwrap_or(None)
    }

    fn known_functions<'a>(datatypes: &'a Vec<DataType>, dict: &'a [Function]) -> impl Iterator<Item=&'a Function> {
        dict.iter().chain(datatypes.iter().flat_map(|d| d.constructors.iter()))
    }

    fn create_graph_example_ids(datatypes: &Vec<DataType>, examples: &IndexMap<DataType, Examples>, dict: &Vec<Function>, ph_count: usize) -> (ThEGraph, IndexMap<DataType, IndexMap<Id, Vec<Id>, RandomState>, RandomState>) {
        let mut egraph = EGraph::default();
        let mut example_ids = IndexMap::new();
        for d in datatypes.iter() {
            example_ids.insert(d.clone(), IndexMap::new());
        }

        for fun in dict.iter()
            .chain(TheSy::collect_phs(TheSy::known_functions(datatypes, dict), ph_count).iter())
            // Hack for supporting bool constant, important for preconditions or and and such.
            .chain(vec![
                // Function::new("true".parse().unwrap(), vec![], "bool".parse().unwrap()),
                // Function::new("false".parse().unwrap(), vec![], "bool".parse().unwrap()),
                Function::new("true".parse().unwrap(), vec![], "Bool".parse().unwrap()),
                Function::new("false".parse().unwrap(), vec![], "Bool".parse().unwrap())].iter())
            .chain(datatypes.iter().flat_map(|d| d.constructors.iter())) {
            let id = egraph.add_expr(&fun.name.parse().unwrap());
            let type_id = egraph.add_expr(&fun.get_type());
            egraph.add(SymbolLang::new("typed", vec![id, type_id]));
            for d in datatypes.iter() {
                example_ids.get_mut(d).unwrap().insert(id, Vec::from_iter(iter::repeat(id).take(examples[d].examples().len())));
            }
        }

        for d in datatypes.iter() {
            let ind_id = egraph.add_expr(&Self::get_ind_var(d).name.parse().unwrap());
            let initial_example_ids = examples[d].examples().iter()
                .map(|e| egraph.add_expr(e)).collect_vec();
            let chained = initial_example_ids.into_iter().collect_vec();
            example_ids.get_mut(d).unwrap().insert(ind_id, chained);
        }
        egraph.rebuild();
        (egraph, example_ids)
    }

    /// Appears at the start of every placeholder var
    pub(crate) const PH_START: &'static str = "ts_ph";

    fn create_apply_rws(dict: &Vec<Function>, datatypes: &Vec<DataType>, ph_count: usize) -> Vec<ThRewrite> {
        let apply_rws = dict.iter()
            .chain(TheSy::collect_phs(TheSy::known_functions(datatypes, dict), ph_count).iter())
            .filter(|fun| !fun.params.is_empty())
            .map(|fun| {
                let params = &fun.params.iter().enumerate()
                    .map(|(i, _x)| format!("?param_{}", i))
                    .collect_vec();
                let name = &fun.name;
                let searcher: Pattern<SymbolLang> = format!("(apply {} {})", name, params.iter().intersperse(&" ".to_string()).cloned().collect::<String>()).parse().unwrap();
                let applier: Pattern<SymbolLang> = format!("({} {})", name, params.iter().intersperse(&" ".to_string()).cloned().collect::<String>()).parse().unwrap();
                rewrite!(format!("apply {}", name); searcher => applier)
            }).collect_vec();
        apply_rws
    }

    /// Create all needed phs from
    fn collect_phs<'a>(known_functions: impl Iterator<Item=&'a Function>, ph_count: usize) -> Vec<Function> {
        let mut res = IndexSet::new();
        for f in known_functions {
            for e in f.params.iter() {
                res.insert(e.clone());
            }
        }
        let mut phs = vec![];
        for d in res {
            for i in 0..ph_count {
                phs.push(Self::get_ph(&d, i));
            }
        }
        phs
    }

    pub(crate) fn get_ph(d: &ThExpr, i: usize) -> Function {
        let s = d.into_tree().to_spaceless_string();
        let name = format!("{}_{}_{}", Self::PH_START, s, i);
        if d.into_tree().root().op.as_str() == "->" {
            let params = d.into_tree().children().iter().dropping_back(1)
                .map(|t| RecExpr::from(t)).collect_vec();
            let ret_type = RecExpr::from(d.into_tree().children().last().unwrap());
            Function::new(name, params, ret_type)
        } else {
            Function::new(name, vec![], d.clone())
        }
    }

    pub(crate) fn get_ind_var(d: &DataType) -> Function {
        Self::get_ph(&d.as_exp(), 0)
    }

    pub fn create_case_splitter(case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Pattern<SymbolLang>, Vec<Pattern<SymbolLang>>)>) -> CaseSplit {
        let mut res = CaseSplit::from_applier_patterns(case_splitters);
        res.extend(consts::system_case_splits());
        res
    }
}

/// *** Thesy ***
impl TheSy {
    fn extract_classes(&self) -> IndexMap<Id, (RepOrder, ThExpr)> {
        let mut ext = Extractor::new(&self.egraph, MinRep);
        // each datatype should have the same keys
        let keys: IndexSet<Id> = self.example_ids.iter().flat_map(|(_d, m)| m.keys()).copied().collect();
        keys.iter().map(|key| {
            let updated_key = &self.egraph.find(*key);
            (*updated_key, ext.find_best(*updated_key))
        }).collect()
    }

    fn fix_example_ids(&mut self) {
        let mut new_ex_ids = IndexMap::new();
        for d in self.example_ids.keys() {
            // new_ex_ids.insert(d, IndexMap::new());
            let t = self.example_ids[d].iter().map(|(k, v)|
                (self.egraph.find(*k), v.iter()
                    .map(|x| self.egraph.find(*x)).collect())).collect();
            new_ex_ids.insert(d.clone(), t);
        }

        self.example_ids = new_ex_ids;
    }

    /// How to efficiently find who merged? Extract one from each ph class then check for its
    /// id the sets of ids the examples are in.
    /// Meaning need to hold all ids for ph and reference it to relevant example ids
    /// You have base case. Create all new ids, for each example lookup params, create edge find all ids from edge
    /// Add anchor only to ind_ph term
    pub fn increase_depth(&mut self) {
        let key = {
            let n = self.egraph.total_number_of_nodes();
            self.stats.init_measure(|| n)
        };
        // First we need to update our keys as they might not be relevant anymore
        self.fix_example_ids();
        // Now apply for all matches
        // let anchor = Self::create_sygue_anchor();
        fn create_edge(op: &String, params: &Vec<(Var, ThExpr)>, sub: &Subst) -> SymbolLang {
            SymbolLang::new(op.clone(), params.iter().map(|(v, _typ)| sub.get(v.clone()).unwrap()).copied().collect())
        }

        fn translate_edge(edge: &SymbolLang, e_index: usize, translations: &IndexMap<Id, Vec<Id>>) -> SymbolLang {
            let new_child = edge.children.iter().map(|id| {
                translations[id][e_index]
            }).collect_vec();
            SymbolLang::new(edge.op.clone(), new_child)
        }

        let op_matches = self.searchers.iter()
            .map(|(op, (searcher, params))| {
                (op, params, searcher.search(&self.egraph).iter_mut().flat_map(|sm| std::mem::take(&mut sm.substs)).collect_vec())
            }).collect_vec();
        for (op, params, subs) in op_matches {
            let typ = {
                let fun = &self.dict.iter().chain(self.datatypes.keys().flat_map(|d| d.constructors.iter()))
                    .find(|f| &f.name == op).unwrap();
                let res: ThExpr = fun.ret_type.clone();
                res
            };
            for sub in subs {
                // Foreach match add a term for ind_ph and foreach example and update example_ids map
                let new_edge = create_edge(op, params, &sub);
                let key = self.egraph.add(new_edge.clone());
                // TODO: do this once per type, not on each sygue application
                let type_key = self.egraph.add_expr(&typ);
                self.egraph.add(SymbolLang::new("typed", vec![key, type_key]));
                // self.egraph.add(SymbolLang::new(anchor.clone(), vec![key]));
                for d in self.datatypes.keys() {
                    let mut new_ids = vec![];
                    for i in 0..self.example_ids[d].iter().next().unwrap().1.len() {
                        new_ids.push(self.egraph.add(translate_edge(&new_edge, i, &self.example_ids[d])));
                    }
                    self.example_ids.get_mut(d).unwrap().insert(key, new_ids);
                }
            }
        }
        self.egraph.rebuild();
        self.stats.update_term_creation(key, self.egraph.total_number_of_nodes());
    }

    pub fn equiv_reduc(&mut self, rules: &mut Vec<ThRewrite>) -> StopReason {
        self.equiv_reduc_depth(rules, self.iter_limit)
    }

    fn equiv_reduc_depth(&mut self, rules: &mut Vec<ThRewrite>, depth: usize) -> StopReason {
        let mut runner = Runner::default().with_time_limit(Duration::from_secs(60 * 10)).with_node_limit(self.node_limit).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(depth);
        // TODO: Support colors
        // if !cfg!(feature = "split_clone") {
        //     runner = runner.with_hook(|runner| {
        //         for pat in case_split::split_patterns.iter() {
        //             for m in pat.search(&runner.egraph) {
        //                 for s in m.substs {
        //                     let colors = s.colors();
        //
        //                 }
        //             }
        //         }
        //         Ok(())
        //     })
        // }
        runner = runner.run(&*rules);
        self.stats.update_rewrite_iters(std::mem::take(&mut runner.iterations));
        self.egraph = runner.egraph;
        self.egraph.rebuild();


        let reason = runner.stop_reason.unwrap();
        self.node_limit = match &reason {
            StopReason::NodeLimit(x) => {
                info!("Reached node limit. Increasing maximum graph size.");
                // TODO: decide dynamically
                x + 50000
            }
            StopReason::Saturated => { self.node_limit }
            x => {
                info!("Stop reason: {:#?}", x);
                self.node_limit
            }
        };
        self.total_iters += runner.iterations.len();
        #[cfg(feature = "stats")]
        sample_graph_stats(&self.egraph, StatsReport::ThesyDepth(self.total_iters));
        reason
    }

    /// For all created terms, get possible equality conjectures.
    /// Uses equivalence classes created by equiv_reduc, and finds classes that
    /// are equal for examples but not for ind_var.
    /// Each such class (e.g. fine class) is represented using a single minimal term.
    /// return the conjectures ordered by representative size.
    pub fn get_conjectures(&mut self) -> Vec<((RepOrder, RepOrder), ThExpr, ThExpr, DataType)> {
        // TODO: make this an iterator to save alot of time during recreating conjectures
        let m_key = self.stats.init_measure(|| 0);
        self.fix_example_ids();
        let finer_classes: IndexMap<DataType, IndexMap<Vec<Id>, IndexSet<Id>>> = self.example_ids.iter().map(|(d, m)| {
            let mut finer_equality_classes: IndexMap<Vec<Id>, IndexSet<Id>> = IndexMap::new();
            for (id, vals) in m {
                if !finer_equality_classes.contains_key(vals) {
                    finer_equality_classes.insert(vals.iter().map(|i| self.egraph.find(*i)).collect_vec(), IndexSet::new());
                }
                finer_equality_classes.get_mut(vals).expect("Should have just added if missing").insert(self.egraph.find(*id));
            }
            (d.clone(), finer_equality_classes)
        }).collect();
        let reps: IndexMap<Id, (RepOrder, ThExpr)> = self.extract_classes();
        let mut res = Vec::new();
        for (d, m) in finer_classes {
            for set in m.values() {
                if set.len() < 2 { continue; }
                for couple in choose(&set.iter().copied().collect_vec()[..], 2) {
                    let max_cop = if reps[couple[0]].0 > reps[couple[1]].0 { (reps[couple[0]].0.clone(), reps[couple[1]].0.clone()) } else { (reps[couple[1]].0.clone(), reps[couple[0]].0.clone()) };
                    res.push((max_cop, reps[couple[0]].1.clone(), reps[couple[1]].1.clone(), d.clone()));
                }
            }
        }
        res.sort_by_key(|x| x.0.clone());
        self.stats.update_conjectures(m_key);
        res.into_iter().rev().collect_vec()
    }

    pub(crate) fn inner_check_equality(rules: &[ThRewrite], precond: &Option<ThExpr>, ex1: &ThExpr, ex2: &ThExpr) -> (Runner<ThNode, ThAnl>, bool) {

        let mut egraph = utils::create_graph(&vec![ex1, ex2]);
        if let Some(pre) = precond {
            utils::add_assumption(&mut egraph, pre);
        }
        let runner = Runner::default()
            .with_iter_limit(8)
            .with_time_limit(Duration::from_secs(600))
            .with_node_limit(10000)
            .with_egraph(egraph)
            .run(rules);
        let res = !runner.egraph.equivs(ex1, ex2).is_empty();
        (runner, res)
    }

    pub fn check_equality(&mut self, rules: &[ThRewrite], precond: &Option<ThExpr>, ex1: &ThExpr, ex2: &ThExpr) -> bool {
        let (mut runner, res) = Self::inner_check_equality(rules, precond, ex1, ex2);
        self.stats.equality_check_iterations.push(std::mem::take(&mut runner.iterations));
        res
    }

    pub fn remaining_goals(&self) -> Option<Vec<Vec<(Option<ThExpr>, ThExpr, ThExpr)>>> {
        return self.goals.clone();
    }

    pub fn check_goals(&mut self, case_splitter: &mut Option<&mut CaseSplit>, rules: &mut Vec<ThRewrite>)
                       -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, ThRewrite)>> {
        if self.goals.is_none() {
            return None;
        }
        let lemmas = self.goals.as_mut().unwrap();
        let mut res = None;
        let mut index = 0;
        'outer: for (i, conjs) in lemmas.iter().enumerate() {
            debug!("Checking goal {}", i);
            for (precond, ex1, ex2) in conjs {
                for p in self.datatypes.values_mut() {
                    let start = if cfg!(feature = "stats") {
                        Some(SystemTime::now())
                    } else { None };
                    res = p.prove_all(case_splitter, rules, Option::from(precond), ex1, ex2);
                    index = i;
                    if res.is_some() {
                        warn!("Proved goal {} - {:?} -> {} = {}", i, precond, ex1, ex2);
                        if cfg!(feature = "stats") {
                            self.stats.goals_proved.push((ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W), SystemTime::now().duration_since(start.unwrap()).unwrap()));
                        }
                        break 'outer;
                    } else {
                        if cfg!(feature = "stats") {
                            self.stats.failed_proofs_goals.push((ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W), SystemTime::now().duration_since(start.unwrap()).unwrap()));
                        }
                    }
                }
            }
        }
        if res.is_some() {
            lemmas.remove(index);
        }
        res
    }

    pub fn run(&mut self, rules: &mut Vec<ThRewrite>, mut case_spliter: Option<CaseSplit>, max_depth: usize) -> Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, ThRewrite)> {
        // TODO: dont allow rules like (take ?x ?y) => (take ?x (append ?y ?y))
        info!("Running TheSy on datatypes: {} dict: {}", self.datatypes.keys().map(|x| &x.name).join(" "), self.dict.iter().map(|x| &x.name).join(" "));
        self.stats.init_run();

        let mut found_rules = vec![];
        let mut splitter_to_use = case_spliter.as_mut();
        for r in &self.system_rws {
            if rules.iter().find(|x| x.name() == r.name()).is_none() {
                rules.push(r.clone());
            }
        }

        warn!("Running prove goals");
        if self.prove_goals(&mut splitter_to_use, rules, &mut found_rules) {
            self.finalize_stats(case_spliter.as_ref());
            return found_rules;
        }

        for depth in 0..max_depth {
            info!("Starting depth {}", depth + 1);
            self.increase_depth();
            let _stop_reason = self.equiv_reduc(rules);

            // True if goals were proven
            if !cfg!(feature="no_expl_split") {
                if splitter_to_use.is_some() {
                    if self.prove_case_split_rules(splitter_to_use.unwrap(), rules, &mut found_rules) {
                        self.finalize_stats(case_spliter.as_ref());
                        return found_rules;
                    }
                    splitter_to_use = case_spliter.as_mut();
                }
            }

            let mut conjectures = self.get_conjectures();

            'outer: while !conjectures.is_empty() {
                let (_, mut ex1, mut ex2, d) = conjectures.pop().unwrap();
                let measure_key = self.stats.init_measure(|| 0);
                let mut new_rules = self.datatypes[&d].prove_ind(&mut splitter_to_use, &rules, &ex1, &ex2);
                if new_rules.is_some() {
                    let temp = new_rules;
                    new_rules = self.datatypes[&d].generalize_prove(&mut splitter_to_use, &rules, &ex1, &ex2);
                    if new_rules.is_none() {
                        new_rules = temp;
                    } else {
                        ex1 = new_rules.as_ref().unwrap()[0].1.pretty_string().parse().unwrap();
                        ex2 = new_rules.as_ref().unwrap()[0].2.pretty_string().parse().unwrap();
                        info!("generalized to {} -- {}", ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W));
                    }
                    if self.check_equality(&rules[..], &None, &ex1, &ex2) {
                        info!("conjecture already known {} = {}", &ex1.pretty(PRETTY_W), &ex2.pretty(PRETTY_W));
                        self.stats.update_filtered_conjecture(&ex1, &ex2);
                        continue 'outer;
                    }
                    self.stats.update_proved(&ex1, &ex2, measure_key);

                    found_rules.extend_from_slice(&new_rules.as_ref().unwrap());
                    for r in new_rules.unwrap() {
                        warn!("proved: {}", r.3.name());
                        // inserting like this so new rule will apply before running into node limit.
                        rules.insert(0, r.3);
                    }

                    warn!("Running prove goals");
                    if self.prove_goals(&mut splitter_to_use, rules, &mut found_rules) {
                        self.finalize_stats(case_spliter.as_ref());
                        return found_rules;
                    }

                    let reduc_depth = 3;
                    let _stop_reason = self.equiv_reduc_depth(rules, reduc_depth);
                    conjectures = self.get_conjectures();
                } else {
                    self.stats.update_failed_proof(ex1, ex2, measure_key);
                }
                self.stats.measures.remove(&measure_key);
            }
        }
        for r in &self.system_rws {
            let i = rules.iter().enumerate().find(|x| x.1.name() == r.name());
            assert!(i.is_some());
            rules.remove(i.unwrap().0);
        }
        self.finalize_stats(case_spliter.as_ref());
        found_rules
    }

    fn prove_case_split_rules(&mut self, case_splitter: &mut CaseSplit, rules: &mut Vec<ThRewrite>, found_rules: &mut Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, ThRewrite)>) -> bool {
        let measure_splits = if cfg!(feature = "stats") {
            let n = case_split::SPLIT_PATTERNS.iter().map(|p|
                p.search(&self.egraph)
                    .iter().map(|m| m.substs.len()).sum::<usize>()
            ).sum();
            self.stats.init_measure(|| n)
        } else {
            0
        };

        let measure_proved = self.stats.init_measure(|| 0);

        let conjs_before_cases = self.get_conjectures();
        // TODO: case split + check all conjectures should be a function.
        // TODO: After finishing checking all conjectures in final depth (if a lemma was found) try case split again then finish.
        // TODO: can be a single loop with max depth
        case_splitter.case_split(
            &mut self.egraph,
            self.case_split_config.split_depth,
            rules,
            self.case_split_config.run_depth,
        );
        // case_split_all(rules, &mut self.egraph, 2, 4);
        self.stats.update_splits(measure_splits);

        let mut splitter_to_use = Some(case_splitter);

        let conjectures = self.get_conjectures();
        let mut changed = false;
        for (_o, mut ex1, mut ex2, d) in conjs_before_cases.into_iter().rev() {
            if conjectures.iter().any(|(_, other_ex1, other_ex2, _)|
                other_ex1 == &ex1 && &ex2 == other_ex2) {
                continue;
            }
            if self.check_equality(&rules[..], &None, &ex1, &ex2) {
                self.stats.update_filtered_conjecture(&ex1, &ex2);
                continue;
            }
            // Might be a false conjecture that just doesnt get picked anymore in reconstruct.
            let mut new_rules = self.datatypes[&d].prove_all(&mut splitter_to_use, rules, None, &ex1, &ex2);
            if new_rules.is_none() {
                continue;
            } else {
                let temp = new_rules;
                new_rules = self.datatypes[&d].generalize_prove(&mut splitter_to_use, &rules, &ex1, &ex2);
                if new_rules.is_none() {
                    new_rules = temp;
                } else {
                    ex1 = new_rules.as_ref().unwrap()[0].1.pretty_string().parse().unwrap();
                    ex2 = new_rules.as_ref().unwrap()[0].2.pretty_string().parse().unwrap();
                    warn!("generalized case_split proof as: {} -- {}", ex1.pretty(PRETTY_W), ex2.pretty(PRETTY_W));
                }
            }
            changed = true;
            self.stats.update_proved(&ex1, &ex2, measure_proved);
            found_rules.extend_from_slice(new_rules.as_ref().unwrap());
            for r in new_rules.unwrap() {
                warn!("proved: {}", r.3.name());
                // inserting like this so new rule will apply before running into node limit.
                rules.insert(0, r.3);
            }
            warn!("Running prove goals");
            if self.prove_goals(&mut splitter_to_use, rules, found_rules) {
                return true;
            }
        }

        if changed {
            let reduc_depth = 3;
            let _stop_reason = self.equiv_reduc_depth(rules, reduc_depth);
        }
        false
    }

    /// Attempt to prove all lemmas with retry. Return true if finished all goals.
    fn prove_goals(&mut self, case_splitter: &mut Option<&mut CaseSplit>, rules: &mut Vec<ThRewrite>, found_rules: &mut Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, ThRewrite)>) -> bool {
        loop {
            let lemma = self.check_goals(case_splitter, rules);
            if lemma.is_none() {
                break;
            }
            found_rules.extend_from_slice(&lemma.as_ref().unwrap());
            for r in lemma.unwrap() {
                info!("proved: {}", r.3.name());
                // inserting like this so new rule will apply before running into node limit.
                rules.insert(0, r.3);
            }
        }
        if self.goals.is_some() && self.goals.as_ref().unwrap().is_empty() {
            warn!("Found all lemmas");
            self.stats.update_total();
            return true;
        }
        false
    }
}

// Stats stuff
impl TheSy {
    pub fn finalize_stats(&mut self, case_spliter: Option<&CaseSplit>) {
        if let Some(cs) = case_spliter {
            self.stats.case_split_stats = cs.stats.clone()
        }
        let mut total_search: f64 = 0.0;
        let mut total_apply: f64 = 0.0;
        let mut total_rebuild: f64 = 0.0;
        let mut all_iters = self.get_prover_iters().into_iter().flatten().into_iter().flatten().collect_vec();
        all_iters.extend(self.stats.equiv_red_iterations.iter().flatten().cloned());
        all_iters.extend(self.stats.case_split_stats.iterations.iter().flatten().cloned());
        for iter in all_iters {
            total_search += iter.search_time;
            total_apply += iter.apply_time;
            total_rebuild += iter.rebuild_time;
        }
        self.stats.total_search_time = Some(total_search);
        self.stats.total_apply_time = Some(total_apply);
        self.stats.total_rebuild_time = Some(total_rebuild);
        self.stats.update_total();
    }
}

#[cfg(test)]
mod test {
    use std::{alloc, iter};
    use std::iter::FromIterator;
    use std::str::FromStr;
    use std::time::SystemTime;

    use cap::Cap;
    use egg::{EGraph, Pattern, RecExpr, Searcher, Symbol, SymbolLang};
    use egg::reconstruct::reconstruct;
    use egg::tools::tools::Grouped;
    use indexmap::{IndexMap, IndexSet};
    #[allow(unused_imports)]
    use invariants::AssertLevel;
    use itertools::Itertools;

    use crate::{PRETTY_W, tests, TheSyConfig};
    use crate::lang::{DataType, Function, ThEGraph, ThRewrite};
    use crate::tests::{init_logging, ProofMode};
    use crate::thesy::{consts, Examples, thesy};
    use crate::thesy::case_split::CaseSplit;
    use crate::thesy::semantics::Definitions;
    use crate::thesy::thesy::TheSy;

    #[global_allocator]
    pub(crate) static ALLOCATOR: Cap<alloc::System> = Cap::new(alloc::System, usize::MAX);

    fn create_nat_type() -> DataType {
        DataType::new("nat".to_string(), vec![
            Function::new("Z".to_string(), vec![], "nat".parse().unwrap()),
            Function::new("S".to_string(), vec!["nat".parse().unwrap()], "nat".parse().unwrap()),
        ])
    }

    fn create_list_type() -> DataType {
        DataType::new("list".to_string(), vec![
            Function::new("Nil".to_string(), vec![], "list".parse().unwrap()),
            Function::new("Cons".to_string(), vec!["nat".parse().unwrap(), "list".parse().unwrap()], "list".parse().unwrap()),
        ])
    }

    fn create_nat_sygue() -> TheSy {
        TheSy::new(
            create_nat_type(),
            Examples::new(&create_nat_type(), 2),
            vec![Function::new("Z".to_string(), vec![], "nat".parse().unwrap()),
                 Function::new("S".to_string(), vec!["nat".parse().unwrap()], "nat".parse().unwrap()),
                 Function::new("pl".to_string(), vec!["nat".parse().unwrap(), "nat".parse().unwrap()], "nat".parse().unwrap())],
        )
    }

    #[allow(dead_code)]
    fn create_list_sygue() -> TheSy {
        TheSy::new(
            create_list_type(),
            Examples::new(&create_list_type(), 2),
            vec![Function::new("snoc".to_string(), vec!["list".parse().unwrap(), "nat".parse().unwrap()], "list".parse().unwrap()),
                 Function::new("rev".to_string(), vec!["list".parse().unwrap()], "list".parse().unwrap()),
                 Function::new("app".to_string(), vec!["list".parse().unwrap(), "list".parse().unwrap()], "list".parse().unwrap())],
        )
    }

    fn create_pl_rewrites() -> Vec<ThRewrite> {
        vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")]
    }

    #[allow(dead_code)]
    fn create_list_rewrites() -> Vec<ThRewrite> {
        vec![
            rewrite!("app base"; "(app Nil ?xs)" => "?xs"),
            rewrite!("app ind"; "(app (Cons ?y ?ys) ?xs)" => "(Cons ?y (app ?ys ?xs))"),
            rewrite!("snoc base"; "(snoc Nil ?x)" => "(Cons ?x Nil)"),
            rewrite!("snoc ind"; "(snoc (Cons ?y ?ys) ?x)" => "(Cons ?y (snoc ?ys ?x))"),
            rewrite!("rev base"; "(rev Nil)" => "Nil"),
            rewrite!("rev ind"; "(rev (Cons ?y ?ys))" => "(snoc (rev ?ys) ?y)"),
        ]
    }

    #[test]
    fn test_no_double_ids() {
        // Note: this is a little slower then usual as there is no equivalence reduction.
        let mut syg = create_nat_sygue();
        let start = SystemTime::now();
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
    }

    #[test]
    fn no_double_translation() {
        // from previous test assume each class has one edge
        let mut syg = create_nat_sygue();
        syg.increase_depth();
        syg.increase_depth();
        let level0 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() == 0)
            .map(|c| (c.id, c.nodes[0].clone()))
            .collect_vec();
        let edges_level0 = level0.iter().map(|c| &c.1).collect::<IndexSet<&SymbolLang>>();
        assert_eq!(edges_level0.len(), level0.len());
        let level1 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level1 = level1.iter().map(|c| c.1).collect::<IndexSet<&SymbolLang>>();
        assert_eq!(edges_level1.len(), level1.len());
        let level2 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.iter().any(|n| level1.iter().find(|x| x.0 == *n).is_some()))
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some() || level1.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level2 = level2.iter().map(|c| c.1).collect::<IndexSet<&SymbolLang>>();
        assert_eq!(edges_level2.len(), level2.len());
    }

    #[test]
    fn test_creates_expected_terms_nat() {
        let nat = create_nat_type();
        let nat_examples = Examples::new(&nat, 2);
        let ex_map = IndexMap::from_iter(iter::once((nat.clone(), nat_examples)));
        let mut syg = {
            TheSy::new_with_ph(
                vec![nat.clone()],
                ex_map,
                vec![Function::new("Z".to_string(), vec![], "nat".parse().unwrap()),
                     Function::new("S".to_string(), vec!["nat".parse().unwrap()], "nat".parse().unwrap()),
                     Function::new("pl".to_string(), vec!["nat".parse().unwrap(), "nat".parse().unwrap()], "nat".parse().unwrap())],
                2,
                None,
                thesy::ITERN,
                None,
                None,
            )
        };
        let z = syg.egraph.lookup(SymbolLang::new("Z", vec![]));
        assert!(z.is_some());
        let sz = syg.egraph.lookup(SymbolLang::new("S", vec![z.unwrap()]));
        assert!(sz.is_some());
        let ssz = syg.egraph.lookup(SymbolLang::new("S", vec![sz.unwrap()]));
        assert!(ssz.is_some());
        let ind_ph = syg.egraph.lookup(SymbolLang::new(TheSy::get_ind_var(&nat).name, vec![]));
        assert!(ind_ph.is_some());
        let ph1 = syg.egraph.lookup(SymbolLang::new(TheSy::get_ph(&nat.as_exp(), 1).name, vec![]));
        assert!(ph1.is_some());
        // let ph2 = syg.egraph.lookup(SymbolLang::new(TheSy::get_ph(&nat.as_exp(), 2).name, vec![]));
        // assert!(ph2.is_some());
        syg.increase_depth();
        let pl_ph1_ex2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ph1.unwrap()), syg.egraph.find(ssz.unwrap())]));
        assert!(pl_ph1_ex2.is_some());
        // let pl_ind_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ind_ph.unwrap()), syg.egraph.find(ph2.unwrap())]));
        // assert!(pl_ind_ph2.is_some());
        // let s_ph2 = syg.egraph.lookup(SymbolLang::new("S", vec![syg.egraph.find(ph2.unwrap())]));
        // assert!(s_ph2.is_some());
        // syg.increase_depth();
        // let pl_pl_ph1_ex2_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(pl_ph1_ex2.unwrap()), syg.egraph.find(ssz.unwrap())]));
        // assert!(pl_pl_ph1_ex2_ph2.is_some());
    }

    #[test]
    fn does_not_create_unneeded_terms() {
        let nat_type = create_nat_type();
        let mut syg = TheSy::new(
            nat_type.clone(),
            Examples::new(&nat_type, 0),
            vec![],
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(typed ?x ?y)").unwrap();
        let results0 = anchor_patt.search(&syg.egraph);
        // Zero, S (functions are also in graph), ph1, ph0, (true false)
        assert_eq!(6usize, results0.iter().map(|x| x.substs.len()).sum::<usize>());
        syg.increase_depth();
        // Zero, S, S Zero, ph1, S ph1, ph0, S ph0, (true false)
        assert_eq!(9usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum::<usize>());
        syg.increase_depth();
        assert_eq!(12usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum::<usize>());

        let new_nat = DataType::new("nat".to_string(), vec![
            Function::new("Z".to_string(), vec![], "nat".parse().unwrap()),
            // Function::new("S".to_string(), vec!["nat".parse().unwrap()], "nat".parse().unwrap()),
        ]);
        let mut syg = TheSy::new_with_ph(
            // For this test dont use full definition
            vec![new_nat.clone()],
            IndexMap::from_iter(iter::once((new_nat.clone(), Examples::new(&new_nat, 0)))),
            vec![Function::new("x".to_string(), vec!["nat".parse().unwrap(), "nat".parse().unwrap()], "nat".parse().unwrap())],
            3,
            None,
            thesy::ITERN,
            None,
            None,
        );

        let results0 = anchor_patt.search(&syg.egraph);
        // Zero, x, ph1, ph0, ph2, (true false)
        assert_eq!(7usize, results0.iter().map(|x| x.substs.len()).sum::<usize>());
        syg.increase_depth();
        let results1 = anchor_patt.search(&syg.egraph);
        // 7 + 16
        assert_eq!(23usize, results1.iter().map(|x| x.substs.len()).sum::<usize>());
        syg.increase_depth();
        // 7 + 16 + 20*20 - 16
        let results2 = anchor_patt.search(&syg.egraph);
        assert_eq!(407usize, results2.iter().map(|x| x.substs.len()).sum::<usize>());
    }

    #[test]
    fn check_representatives_sane() {
        let mut syg = create_nat_sygue();
        let mut rewrites = create_pl_rewrites();

        syg.increase_depth();
        syg.equiv_reduc(&mut rewrites);
        syg.increase_depth();
        syg.equiv_reduc(&mut rewrites);
        let classes = syg.extract_classes();
        for (_, (_, exp)) in classes {
            for n in exp.as_ref() {
                if n.op.to_string() == "pl" && !n.children.is_empty() {
                    let index = n.children[0].to_string();
                    assert_ne!(exp.as_ref()[index.parse::<usize>().unwrap()].op.to_string(), "Z");
                }
            }
        }
    }

    #[test]
    fn check_conjectures_sane() {
        let mut syg = create_nat_sygue();
        let mut rewrites = create_pl_rewrites();

        syg.increase_depth();
        syg.equiv_reduc(&mut rewrites);
        syg.increase_depth();
        syg.equiv_reduc(&mut rewrites);
        let conjectures = syg.get_conjectures().into_iter().map(|x| (x.1, x.2)).collect_vec();
        println!("{}", conjectures.iter().map(|x| x.0.to_string() + " ?= " + &*x.1.to_string()).intersperse("\n".parse().unwrap()).collect::<String>());
        for c in conjectures.iter().map(|x| x.0.to_string() + " ?= " + &*x.1.to_string()) {
            assert_ne!(c, "ind_var ?= ts_ph0");
            assert_ne!(c, "ts_ph0 ?= ind_var");
            assert_ne!(c, "ind_var ?= ts_ph1");
            assert_ne!(c, "ts_ph1 ?= ts_ph0");
            assert_ne!(c, "ts_ph0 ?= ts_ph1");
            assert_ne!(c, "ts_ph0 ?= ts_ph0");
            assert_ne!(c, "(pl ts_ph0 ind_var) ?= (pl ts_ph1 ind_var)");
            assert_ne!(c, "(pl ind_var ts_ph0) ?= (pl ts_ph1 ind_var)");
            assert_ne!(c, "(pl ts_ph0 ind_var) ?= (pl ind_var ts_ph1)");
            assert_ne!(c, "(pl ind_var ts_ph0) ?= (pl ind_var ts_ph1)");
            assert_ne!(c, "(pl ts_ph1 ind_var) ?= (pl ts_ph0 ind_var)");
            assert_ne!(c, "(pl ind_var ts_ph1) ?= (pl ts_ph0 ind_var)");
            assert_ne!(c, "(pl ts_ph1 ind_var) ?= (pl ind_var ts_ph0)");
            assert_ne!(c, "(pl ind_var ts_ph1) ?= (pl ind_var ts_ph0)");
        }
    }

    #[test]
    fn prove_pl_zero() {
        let mut syg = create_nat_sygue();
        let nat = create_nat_type();
        let rewrites = create_pl_rewrites();
        let ind_rec = TheSy::get_ind_var(&nat);
        assert!(syg.datatypes[&nat].prove_ind(&mut None, &rewrites[..], &format!("(pl {} Z)", ind_rec.name).parse().unwrap(), &ind_rec.name.parse().unwrap()).is_some())
    }

    fn filter_definitions() -> Definitions {
        let mut list_defs = Definitions::from_file(&"theories/list.th".parse().unwrap());
        let filter_defs = Definitions::from_file(&"tests/filter.th".parse().unwrap());
        list_defs.merge(filter_defs);
        list_defs
    }

    #[test]
    fn create_filter_p_filter_q() {
        let (list_type, dict, mut thesy) = create_filter_thesy();
        thesy.increase_depth();
        thesy.increase_depth();
        let phs = TheSy::collect_phs(dict.iter().chain(list_type.constructors.iter()), 3).into_iter().filter(|x| !x.params.is_empty()).collect_vec();
        let pat1 = Pattern::from_str(&*format!("(filter {} (filter {} {}))", phs[0].name, phs[1].name, TheSy::get_ind_var(&list_type).name)).unwrap();
        let pat2 = Pattern::from_str(&*format!("(filter {} (filter {} {}))", phs[1].name, phs[0].name, TheSy::get_ind_var(&list_type).name)).unwrap();
        assert!(!pat1.search(&thesy.egraph).is_empty());
        assert!(!pat2.search(&thesy.egraph).is_empty());
    }

    fn create_filter_thesy() -> (DataType, Vec<Function>, TheSy) {
        let list_type = create_list_type();
        let dict = vec![Function::new("filter".to_string(),
                                      vec!["(-> nat bool)", "list"].into_iter()
                                          .map(|x| x.parse().unwrap()).collect_vec(),
                                      "list".parse().unwrap(),
        )];
        let thesy = TheSy::new(list_type.clone(), Examples::new(&list_type, 2), dict.clone());
        (list_type, dict, thesy)
    }

    #[test]
    fn filter_p_filter_q_conjecture() {
        init_logging();
        invariants::set_max_level(AssertLevel::Off);

        let mut filter_defs = filter_definitions();
        filter_defs.functions = filter_defs.functions.into_iter().filter(|f| f.name == "filter".to_string()).collect_vec();

        let proof = tests::test_terms(filter_defs.clone());


        // let mut thesy = TheSy::from(&filter_defs);
        // filter_defs.rws.extend(thesy.system_rws.iter().cloned());
        // thesy.increase_depth();
        // thesy.equiv_reduc(&mut filter_defs.rws);
        // thesy.increase_depth();
        // thesy.equiv_reduc(&mut filter_defs.rws);
        //
        // thesy.egraph.rebuild();
        // assert!(filter_p_filter_q_exists(&thesy.egraph, 1));
        //
        // let mut case_splitter = TheSy::create_case_splitter(filter_defs.case_splitters);
        // case_splitter.extend(consts::system_case_splits());
        //
        // case_splitter.case_split(&mut thesy.egraph, 4, &filter_defs.rws, 4);
        // let conjs = thesy.get_conjectures();
        // assert!(conjs.iter().any(|(o, c1, c2, d)| {
        //     (c1.pretty(500) == "(filter ts_ph_POfn_Nat_boolPC_0 (filter ts_ph_POfn_Nat_boolPC_1 ts_ph_Lst_0))"
        //         && c2.pretty(500) == "(filter ts_ph_POfn_Nat_boolPC_1 (filter ts_ph_POfn_Nat_boolPC_0 ts_ph_Lst_0))")
        //         || (c2.pretty(500) == "(filter ts_ph_POfn_Nat_boolPC_0 (filter ts_ph_POfn_Nat_boolPC_1 ts_ph_Lst_0))"
        //         && c1.pretty(500) == "(filter ts_ph_POfn_Nat_boolPC_1 (filter ts_ph_POfn_Nat_boolPC_0 ts_ph_Lst_0))")
        // }));
        assert_ne!(proof, ProofMode::Failed);
        assert_ne!(proof, ProofMode::TermNotCreated);
        assert_ne!(proof, ProofMode::ExamplesFailed);
        assert_eq!(proof, ProofMode::Prover);
    }

    #[test]
    #[ignore]
    fn split_case_filter_p_and_q() {}

    #[test]
    fn take_drop_equiv_red() {
        init_logging();

        let mut conf = TheSyConfig::from_path("theories/goal1.smt2.th".parse().unwrap());
        let mut thesy = TheSy::from(&conf);
        let mut case_split = TheSy::create_case_splitter(conf.definitions.case_splitters);
        let mut rules = std::mem::take(&mut conf.definitions.rws);
        let nil = thesy.egraph.add_expr(&"nil".parse().unwrap());
        let consx = thesy.egraph.add_expr(&"(cons x nil)".parse().unwrap());
        let consxy = thesy.egraph.add_expr(&"(cons y (cons x nil))".parse().unwrap());
        let ex0 = thesy.egraph.add_expr(&"(append (take i nil) (drop i nil))".parse().unwrap());
        let ex1 = thesy.egraph.add_expr(&"(append (take i (cons x nil)) (drop i (cons x nil)))".parse().unwrap());
        let dropix = thesy.egraph.add_expr(&"(drop i (cons x nil))".parse().unwrap());
        let ex2 = thesy.egraph.add_expr(&"(append (take i (cons y (cons x nil))) (drop i (cons y (cons x nil))))".parse().unwrap());
        info!("Starting first rebuild");
        thesy.egraph.rebuild();
        info!("Done first rebuild");
        thesy.equiv_reduc(&mut rules);
        info!("Done eq reduction");
        thesy.egraph.rebuild();
        info!("Done second rebuild");
        // assert_ne!(egraph.find(nil), egraph.find(ex0));
        assert_ne!(thesy.egraph.find(consx), thesy.egraph.find(ex1));
        assert_ne!(thesy.egraph.find(consxy), thesy.egraph.find(ex2));
        assert_eq!(thesy.egraph.find(nil), thesy.egraph.find(ex0));
        println!("Currently (before) allocated: {}MB", ALLOCATOR.allocated() as f64 / 1e6);
        info!("Starting case split");
        case_split.case_split(&mut thesy.egraph, 2, &rules, 6);
        println!("Currently (after) allocated: {}MB", ALLOCATOR.allocated() as f64 / 1e6);
        info!("Done case split");
        thesy.egraph.rebuild();
        println!("drop i [x] is {}", thesy.egraph.find(dropix));
        info!("Done third and final rebuild");
        assert_eq!(thesy.egraph.find(consx), thesy.egraph.find(ex1));

        let dropiyx = thesy.egraph.add_expr(&"(drop i (cons y (cons x nil)))".parse().unwrap());
        let takeiyx = thesy.egraph.add_expr(&"(take i (cons y (cons x nil)))".parse().unwrap());
        let dropix = thesy.egraph.add_expr(&"(drop i (cons x nil))".parse().unwrap());
        thesy.egraph.rebuild();

        println!("Black results:");
        println!("\tnil: {}", nil);
        println!("\tconsx: {}", consx);
        println!("\tconsxy: {}", consxy);
        println!("\tex0: {}", ex0);
        println!("\tex1: {}", ex1);
        println!("\tex2: {}", ex2);
        println!("drop i [y, x]: {}", dropiyx);
        println!("take i [y, x]: {}", takeiyx);
        println!("drop i [x]: {}", dropix);

        for c in thesy.egraph.colors() {
            println!("Color {} results:", c.get_id());
            println!("\tnil: {}", thesy.egraph.colored_find(c.get_id(), nil));
            println!("\tconsx: {}", thesy.egraph.colored_find(c.get_id(), consx));
            println!("\tconsxy: {}", thesy.egraph.colored_find(c.get_id(), consxy));
            println!("\tex0: {}", thesy.egraph.colored_find(c.get_id(), ex0));
            println!("\tex1: {}", thesy.egraph.colored_find(c.get_id(), ex1));
            println!("\tex2: {}", thesy.egraph.colored_find(c.get_id(), ex2));
            println!("\tdrop i [y, x]: {}", thesy.egraph.colored_find(c.get_id(), dropiyx));
            println!("\ttake i [y, x]: {}", thesy.egraph.colored_find(c.get_id(), takeiyx));
            println!("\tdrop i [x]: {}", thesy.egraph.colored_find(c.get_id(), dropix));
        }

        thesy.egraph.dot().to_dot("black_take_drop.dot").unwrap();

        assert_eq!(thesy.egraph.find(consxy), thesy.egraph.find(ex2));
        // {?x52: 70, ?y53: 48, ?z: 47 color: 14}
    }

    // #[test]
    // fn take_drop_prove_all() {
    //     let mut conf = TheSyConfig::from_path("theories/goal1.smt2.th".parse().unwrap());
    //     let (thesy, mut rules) = conf.run(Some(2));
    //     assert!(thesy.datatypes[conf.definitions.datatypes.last().unwrap()].prove_all(&*rules, &"(append (take ts_ph_Nat_1 ts_ph_Lst_0) (drop ts_ph_Nat_1 ts_ph_Lst_0))".parse().unwrap(), &"ts_ph_Lst_0".parse().unwrap()).is_some());
    // }


    #[test]
    fn test_ite_split_rule() {
        let mut egraph: ThEGraph = EGraph::default();
        egraph.add_expr(&RecExpr::from_str("(ite z x y)").unwrap());
        egraph.rebuild();
        let mut case_splitters: CaseSplit = consts::system_case_splits();
        assert!(!case_splitters.find_splitters(&mut egraph).is_empty());
    }

    fn check_types_not_merged(egraph: &ThEGraph) {
        egraph.classes().flat_map(|c| c.iter()
            .filter(|n| n.op == Symbol::from_str("typed").unwrap()))
            .grouped(|x| {
                assert_eq!(x.children.len(), 2);
                x.children[0]
            }).iter().for_each(|(id, edges)| {
            assert_eq!(1, edges.len(),
                       "Type {} (reconstructed as {}) has {} edges: {:#?}",
                       id,
                       reconstruct(&egraph, *id, 3).unwrap().pretty(PRETTY_W),
                       edges.len(),
                       edges);
        });
    }

    #[test]
    fn test_all_are_single_typed() {
        init_logging();

        let mut config = TheSyConfig::from_path("theories/list.th".parse().unwrap());
        let mut thesy = TheSy::from(&config);
        thesy.increase_depth();
        thesy.increase_depth();
        check_types_not_merged(&thesy.egraph);
        config.definitions.rws.extend_from_slice(&thesy.system_rws);
        thesy.equiv_reduc_depth(&mut config.definitions.rws, 20);
        check_types_not_merged(&thesy.egraph);
    }

    #[test]
    fn test_not_creating_append_nat() {
        let config = TheSyConfig::from_path("theories/list.th".parse().unwrap());
        let mut thesy = TheSy::from(&config);
        thesy.increase_depth();
        thesy.increase_depth();
    }

    #[test]
    fn test_list_run_append_assoc() {
        init_logging();
        // invariants::set_max_level(AssertLevel::Off);
        let mut config = TheSyConfig::from_path("theories/list.th".parse().unwrap());
        let mut thesy = TheSy::from(&config);
        thesy.run(&mut config.definitions.rws, None, 2);
        assert_eq!(config.definitions.datatypes.len(), 1);
        let res = thesy.check_equality(&config.definitions.rws, &None, &"(append x (append y z))".parse().unwrap(), &"(append (append x y) z)".parse().unwrap());
        assert!(res);
    }

    #[test]
    fn test_prove_split_and_or() {
        init_logging();

        let defs = TheSyConfig::from_path("tests/booleans.th".to_string()).definitions;
        let proofs = tests::test_prover(&defs);
        assert!(!proofs.1.contains(&ProofMode::Failed));
    }

    #[test]
    fn test_split_and_or() {
        init_logging();
        // invariants::set_max_level(AssertLevel::Off);
        let mut defs = TheSyConfig::from_path("tests/booleans.th".to_string()).definitions;
        let conjectures = std::mem::take(&mut defs.conjectures);
        let goals = std::mem::take(&mut defs.goals);
        for (c, g) in conjectures.into_iter().zip(goals.into_iter()) {
            let proof_text = format!("proving {}{} = {}",
                                     g.0.as_ref().map_or("".to_string(), |e| e.to_string() + "|> "),
                                     &g.1,
                                     &g.2);
            info!("{}", proof_text);
            defs.goals = vec![g];
            defs.conjectures = vec![c];
            let proof = tests::test_terms(defs.clone());
            warn!("Proof mode {:?} for {}", proof, proof_text);
            assert_ne!(ProofMode::ExamplesFailed, proof, "Examples failed for {}", proof_text);
            assert_ne!(ProofMode::Failed, proof, "Proof failed for {}", proof_text);
            assert_ne!(ProofMode::TermNotCreated, proof, "Terms not created for {}", proof_text);
        }
    }

    #[test]
    fn test_split_minus_plus() {
        init_logging();
        invariants::set_max_level(AssertLevel::Off);
        let mut defs = TheSyConfig::from_path("tests/minus.th".to_string()).definitions;
        let conjectures = std::mem::take(&mut defs.conjectures);
        let goals = std::mem::take(&mut defs.goals);
        for (c, g) in conjectures.into_iter().zip(goals.into_iter()) {
            info!("proving {}{} = {}",
                  g.0.as_ref().map_or("".to_string(), |e| e.to_string() + "|> "),
                  &g.1,
                  &g.2);
            defs.goals = vec![g];
            defs.conjectures = vec![c];
            let proof = tests::test_terms(defs.clone());
            assert_ne!(ProofMode::ExamplesFailed, proof);
            assert_ne!(ProofMode::Failed, proof);
            assert_ne!(ProofMode::TermNotCreated, proof);
        }
    }

    #[test]
    fn test_split_filter_p() {
        init_logging();

        let mut defs = Definitions::from_file(&"tests/filter.th".parse().unwrap());
        let conjectures = std::mem::take(&mut defs.conjectures);
        let goals = std::mem::take(&mut defs.goals);
        for (c, g) in conjectures.into_iter().zip(goals.into_iter()) {
            info!("proving {}{} = {}",
                  g.0.as_ref().map_or("".to_string(), |e| e.to_string() + "|> "),
                  &g.1,
                  &g.2);
            defs.goals = vec![g];
            defs.conjectures = vec![c];
            let proof = tests::test_terms(defs.clone());
            println!("{:?}", proof);
            assert_ne!(ProofMode::ExamplesFailed, proof);
            assert_ne!(ProofMode::Failed, proof);
            //assert_ne!(ProofMode::TermNotCreated, proof);
        }
    }

    #[test]
    fn test_rotate7() {
        init_logging();

        let defs = Definitions::from_file(&"tests/rotate-goal7.th".parse().unwrap());
        let (_thesy, res) = tests::test_prover(&defs);
        assert!(!res.contains(&ProofMode::Prover));
    }
}
