use std::rc::Rc;
use egg::*;
use std::iter;
use itertools::Itertools;
use crate::eggstentions::multisearcher::multisearcher::{MultiDiffSearcher, MultiEqSearcher};
use std::str::FromStr;
use std::time::{Duration, SystemTime};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;
use crate::eggstentions::costs::{MinRep, RepOrder};
use crate::tools::tools::choose;
use crate::eggstentions::appliers::DiffApplier;
use log::{info, warn, trace, debug};
use egg::test::run;
use crate::eggstentions::expression_ops::{RecExpSlice, IntoTree, Tree};
use std::collections::hash_map::RandomState;

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct DataType {
    pub name: String,
    pub type_params: Vec<RecExpr<SymbolLang>>,
    // TODO: change to Function instead of rec expr
    /// Constructor name applied on types
    pub constructors: Vec<Function>,
}

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<RecExpr<SymbolLang>>,
    /// Constructor name applied on types
    pub ret_type: RecExpr<SymbolLang>,
}

impl Function {
    pub fn new(name: String, params: Vec<RecExpr<SymbolLang>>, ret_type: RecExpr<SymbolLang>) -> Function {
        Function { name, params, ret_type }
    }

    pub fn as_exp(&self) -> RecExpr<SymbolLang> {
        let as_type = self.get_type();
        let mut children = as_type.as_ref().iter().cloned().dropping_back(1).collect_vec();
        let mut new_last = as_type.as_ref().last().unwrap().clone();
        new_last.op = Symbol::from(self.name.clone());
        children.push(new_last);
        RecExpr::from(children)
    }

    pub fn get_type(&self) -> RecExpr<SymbolLang> {
        let mut children = vec![];
        let mut indices = vec![];
        for p in &self.params {
            children.extend_from_slice(p.as_ref());
            indices.push(Id::from(children.len() - 1));
        }
        if children.is_empty() {
            self.ret_type.clone()
        } else {
            children.extend_from_slice(self.ret_type.as_ref());
            indices.push(Id::from(children.len() - 1));
            children.push(SymbolLang::new("->", indices));
            RecExpr::from(children)
        }
    }

    pub fn apply_params(&self, params: Vec<RecExpr<SymbolLang>>) -> RecExpr<SymbolLang> {
        let mut res = RecExpr::default();
        let mut indices = vec![];
        for p in params {
            let current_len = res.as_ref().len();
            for s in p.as_ref() {
                res.add(s.clone().map_children(|c| Id::from(usize::from(c) + current_len)));
            }
            indices.push(Id::from(res.as_ref().len() - 1));
        }
        res.add(SymbolLang::new(self.name.clone(), indices));
        res
    }
}

impl From<RecExpr<SymbolLang>> for Function {
    fn from(exp: RecExpr<SymbolLang>) -> Self {
        let tree = exp.into_tree();
        Function::new(tree.root().op.to_string(),
                      tree.children().iter().dropping_back(1)
                          .map(|t| RecExpr::from(t)).collect_vec(),
                      RecExpr::from(tree.children().last().unwrap()))
    }
}

impl DataType {
    pub(crate) fn new(name: String, constructors: Vec<Function>) -> DataType {
        DataType { name, type_params: vec![], constructors }
    }

    pub fn generic(name: String, type_params: Vec<RecExpr<SymbolLang>>, constructors: Vec<Function>) -> DataType {
        DataType { name, type_params, constructors }
    }

    pub fn as_exp(&self) -> RecExpr<SymbolLang> {
        let mut res = vec![];
        let children = self.type_params.iter().map(|e| {
            res.extend(e.as_ref().iter().cloned());
            Id::from(res.len() - 1)
        }).collect_vec();
        res.push(SymbolLang::new(self.name.clone(), children));
        RecExpr::from(res)
    }
}

pub struct TheSy {
    /// known datatypes to wfo rewrites for induction
    datatypes: HashMap<DataType, Vec<Rewrite<SymbolLang, ()>>>,
    /// known function declerations and their types
    dict: Vec<(String, RecExpr<SymbolLang>)>,
    /// egraph which is expanded as part of the exploration
    pub egraph: EGraph<SymbolLang, ()>,
    /// searchers used to create the next depth of terms
    searchers: HashMap<String, (MultiDiffSearcher, Vec<(Var, RecExpr<SymbolLang>)>)>,
    /// map maintaining the connection between eclasses created by sygue
    /// and their associated eclasses with `ind_ph` replaced by symbolic examples.
    example_ids: HashMap<DataType, HashMap<Id, Vec<Id>>>,
    /// Flattern apply rewrites are used for high order function such as fold.
    /// TODO: add support for partial application
    apply_rws: Vec<Rewrite<SymbolLang, ()>>,
    /// Rewrites to support ite
    ite_rws: Vec<Rewrite<SymbolLang, ()>>,
    /// Limits to use in equiv reduc
    node_limit: usize,
    /// Limits to use in equiv reduc
    iter_limit: usize,
}

/// *** Thesy ***
impl TheSy {
    pub fn new(datatype: DataType, examples: Vec<RecExpr<SymbolLang>>, dict: Vec<(String, RecExpr<SymbolLang>)>) -> TheSy {
        Self::new_with_ph(vec![datatype.clone()], HashMap::from_iter(iter::once((datatype, examples))), dict, 3)
    }

    pub fn new_with_ph(datatypes: Vec<DataType>, examples: HashMap<DataType, Vec<RecExpr<SymbolLang>>>, dict: Vec<(String, RecExpr<SymbolLang>)>, ph_count: usize) -> TheSy {
        // TODO: automatic examples
        let datatype_to_wfo: HashMap<DataType, Vec<Rewrite<SymbolLang, ()>>, RandomState> = datatypes.iter()
            .map(|d| (d.clone(), Self::wfo_datatype(d))).collect();
        let mut egraph = EGraph::default();
        let mut example_ids = HashMap::new();
        for d in datatypes.iter() {
            example_ids.insert(d.clone(), HashMap::new());
        }
        for (name, typ) in dict.iter()
            .chain(TheSy::collect_phs(&dict, ph_count).iter()) {
            let id = egraph.add_expr(&name.parse().unwrap());
            let type_id = egraph.add_expr(typ);
            egraph.add(SymbolLang::new("typed", vec![id, type_id]));
            for d in datatypes.iter() {
                example_ids.get_mut(d).unwrap().insert(id, Vec::from_iter(iter::repeat(id).take(examples[d].len())));
            }
        }

        let apply_rws = dict.iter()
            .chain(TheSy::collect_phs(&dict, ph_count).iter())
            .filter(|(name, typ)| typ.into_tree().root().op.to_string() == "->".to_string())
            .map(|(name, typ)| {
                let params = typ.into_tree().children()
                    .iter().dropping_back(1).enumerate()
                    .map(|(i, x)| format!("?param_{}", i))
                    .collect_vec();
                let searcher: Pattern<SymbolLang> = format!("(apply {} {})", name, params.iter().intersperse(&" ".to_string()).cloned().collect::<String>()).parse().unwrap();
                let applier: Pattern<SymbolLang> = format!("({} {})", name, params.iter().intersperse(&" ".to_string()).cloned().collect::<String>()).parse().unwrap();
                rewrite!(format!("apply {}", name); searcher => applier)
            }).collect_vec();

        let ite_rws: Vec<Rewrite<SymbolLang, ()>> = vec![
            rewrite!("ite_true"; "(ite true ?x ?y)" => "?x"),
            rewrite!("ite_false"; "(ite false ?x ?y)" => "?y")
        ];

        for d in datatypes.iter() {
            let ind_id = egraph.add_expr(&Self::get_ind_var(d).parse().unwrap());
            let initial_example_ids = examples[d].iter()
                .map(|e| egraph.add_expr(e)).collect_vec();
            let chained = initial_example_ids.into_iter().collect_vec();
            example_ids.get_mut(d).unwrap().insert(ind_id, chained);
        }

        let mut res = TheSy {
            datatypes: datatype_to_wfo,
            dict,
            egraph,
            // sygue_rules: vec![],
            searchers: HashMap::new(),
            example_ids,
            apply_rws,
            ite_rws,
            node_limit: 400000,
            iter_limit: 8,
        };

        res.searchers = res.create_sygue_serchers();
        res.egraph.rebuild();
        res
    }

    fn extract_classes(&self) -> HashMap<Id, (RepOrder, RecExpr<SymbolLang>)> {
        let mut ext = Extractor::new(&self.egraph, MinRep);
        // each datatype should have the same keys
        let keys: HashSet<Id> = self.example_ids.iter().flat_map(|(d, m)| m.keys()).copied().collect();
        keys.iter().map(|key| {
            let updated_key = &self.egraph.find(*key);
            (*updated_key, ext.find_best(*updated_key))
        }).collect()
    }

    fn create_sygue_anchor() -> String {
        format!("sygueanchor")
    }

    fn create_sygue_serchers(&self) -> HashMap<String, (MultiDiffSearcher, Vec<(Var, RecExpr<SymbolLang>)>)> {
        let mut res = HashMap::new();
        self.dict.iter().for_each(|(fun_name, fun_type)| {
            let type_tree = fun_type.into_tree();
            if type_tree.root().op.to_string() == "->" {
                let params: Vec<(Var, RecExpr<SymbolLang>)> = type_tree.children().iter().enumerate()
                    .dropping_back(1).map(|(i, t)| {
                    (Var::from_str(&*format!("?param_{}", i)).unwrap(), t.into())
                }).collect_vec();
                let patterns = params.iter()
                    .flat_map(|(v, typ)| {
                        vec![
                            Pattern::from_str(&*format!("(typed {} {})", v.to_string(), typ.pretty(500))).unwrap(),
                        ]
                    }).collect::<Vec<Pattern<SymbolLang>>>();
                res.insert(fun_name.clone(), (MultiDiffSearcher::new(patterns), params));
            }
        });
        res
    }

    fn fix_example_ids(&mut self) {
        let mut new_ex_ids = HashMap::new();
        for d in self.example_ids.keys() {
            // new_ex_ids.insert(d, HashMap::new());
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
        // First we need to update our keys as they might not be relevant anymore
        self.fix_example_ids();
        // Now apply for all matches
        // let anchor = Self::create_sygue_anchor();
        fn create_edge(op: &String, params: &Vec<(Var, RecExpr<SymbolLang>)>, sub: &Subst) -> SymbolLang {
            SymbolLang::new(op.clone(), params.iter().map(|(v, typ)| sub.get(v.clone()).unwrap()).copied().collect())
        }

        fn translate_edge(edge: &SymbolLang, e_index: usize, translations: &HashMap<Id, Vec<Id>>) -> SymbolLang {
            let new_child = edge.children.iter().map(|id| {
                translations[id][e_index]
            }).collect_vec();
            SymbolLang::new(edge.op.clone(), new_child)
        }

        let op_matches = self.searchers.iter()
            .map(|(op, (searcher, params))| {
                (op, params, searcher.search(&self.egraph).iter_mut().flat_map(|mut sm| std::mem::take(&mut sm.substs)).collect_vec())
            }).collect_vec();
        for (op, params, subs) in op_matches {
            let typ = {
                let full_type = &self.dict.iter()
                    .find(|(n, typ)| n == op).unwrap().1.into_tree();
                let res: RecExpr<SymbolLang> = full_type.children().last().unwrap().into();
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
    }

    pub fn equiv_reduc(&mut self, rules: &[Rewrite<SymbolLang, ()>]) -> StopReason {
        self.equiv_reduc_depth(rules, self.iter_limit)
    }

    fn equiv_reduc_depth(&mut self, rules: &[Rewrite<SymbolLang, ()>], depth: usize) -> StopReason {
        let mut runner = Runner::default().with_time_limit(Duration::from_secs(60 * 10)).with_node_limit(self.node_limit).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(depth);
        runner = runner.run(rules);
        // for (i, it) in runner.iterations.iter().enumerate() {
        //     println!("Info on iteration {}:", i);
        //     println!("Rebuilding time {}", it.rebuild_time);
        //     println!("Search time {}", it.search_time);
        //     for x in &it.applied {
        //         println!("Rule {} time {}", x.0, x.1);
        //     }
        //     println!();
        // }
        self.egraph = runner.egraph;
        self.egraph.rebuild();
        runner.stop_reason.unwrap()
    }

    /// For all created terms, get possible equality conjectures.
    /// Uses equivalence classes created by equiv_reduc, and finds classes that
    /// are equal for examples but not for ind_var.
    /// Each such class (e.g. fine class) is represented using a single minimal term.
    /// return the conjectures ordered by representative size.
    pub fn get_conjectures(&mut self) -> Vec<(RepOrder, RecExpr<SymbolLang>, RecExpr<SymbolLang>, DataType)> {
        // TODO: make this an iterator to save alot of time during recreating conjectures
        self.fix_example_ids();
        let finer_classes: HashMap<DataType, HashMap<Vec<Id>, HashSet<Id>>> = self.example_ids.iter().map(|(d, m)| {
            let mut finer_equality_classes: HashMap<Vec<Id>, HashSet<Id>> = HashMap::new();
            for (id, vals) in m {
                if !finer_equality_classes.contains_key(vals) {
                    finer_equality_classes.insert(vals.iter().map(|i| self.egraph.find(*i)).collect_vec(), HashSet::new());
                }
                finer_equality_classes.get_mut(vals).expect("Should have just added if missing").insert(self.egraph.find(*id));
            }
            (d.clone(), finer_equality_classes)
        }).collect();
        let reps = self.extract_classes();
        let mut res = Vec::new();
        for (d, m) in finer_classes {
            for set in m.values() {
                if set.len() < 2 { continue; }
                for couple in choose(&set.iter().collect_vec()[..], 2) {
                    let max = if reps[couple[0]].0 >= reps[couple[1]].0 { reps[couple[0]].0.clone() } else { reps[couple[1]].0.clone() };
                    res.push((max, reps[couple[0]].1.clone(), reps[couple[1]].1.clone(), d.clone()));
                }
            }
        }
        res.sort_by_key(|x| x.0.clone());
        res.into_iter().rev().collect_vec()
    }

    /// Assume base case is correct and prove equality using induction.
    /// Induction hypothesis is given as a rewrite rule, using precompiled rewrite rules
    /// representing well founded order on the induction variable.
    /// Need to replace the induction variable with an expression representing a constructor and
    /// well founded order on the params of the constructor.
    pub fn prove(&self, rules: &[Rewrite<SymbolLang, ()>], datatype: &DataType, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Option<Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        if ex1.as_ref().iter().find(|s| s.op.to_string() == Self::get_ind_var(datatype)).is_none() &&
            ex2.as_ref().iter().find(|s| s.op.to_string() == Self::get_ind_var(datatype)).is_none() {
            return None;
        }
        // rewrites to encode proof
        let mut rule_set = Self::create_hypothesis(&Self::get_ind_var(datatype), &ex1, &ex2);
        let wfo_rws = self.datatypes.get(&datatype).unwrap();
        rule_set.extend(rules.iter().cloned());
        rule_set.extend(wfo_rws.iter().cloned());
        // create graph containing both expressions
        let mut orig_egraph: EGraph<SymbolLang, ()> = EGraph::default();
        let ex1_id = orig_egraph.add_expr(&ex1);
        let ex2_id = orig_egraph.add_expr(&ex2);
        let ind_id = orig_egraph.lookup(SymbolLang::new(&Self::get_ind_var(datatype), vec![])).unwrap();
        let mut res = true;
        for c in datatype.constructors.iter().filter(|c| !c.params.is_empty()) {
            let mut egraph = orig_egraph.clone();
            let contr_exp = RecExpr::from_str(format!("({} {})", c.name, c.params.iter().enumerate()
                .map(|(i, t)| "param_".to_owned() + &*i.to_string())
                .intersperse(" ".parse().unwrap()).collect::<String>()).as_str()).unwrap();
            let contr_id = egraph.add_expr(&contr_exp);
            egraph.union(contr_id, ind_id);
            let mut runner: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).with_iter_limit(8).run(&rule_set[..]);
            Self::case_split_all(rules, &mut runner.egraph, 2, 4);
            res = res && !runner.egraph.equivs(&ex1, &ex2).is_empty()
        }
        if res {
            let fixed_ex1 = Self::pattern_from_exp(ex1, &Self::get_ind_var(datatype), &("?".to_owned() + &Self::get_ind_var(datatype)));
            let fixed_ex2 = Self::pattern_from_exp(ex2, &Self::get_ind_var(datatype), &("?".to_owned() + &Self::get_ind_var(datatype)));
            let text1 = fixed_ex1.pretty(80) + " => " + &*fixed_ex2.pretty(80);
            let text2 = fixed_ex2.pretty(80) + " => " + &*fixed_ex1.pretty(80);
            let mut new_rules = vec![];
            // println!("proved: {}", text1);
            // TODO: dont do it so half assed
            if text1.starts_with("(") {
                let rw = Rewrite::new(text1.clone(), text1.clone(), fixed_ex1.clone(), fixed_ex2.clone());
                if rw.is_ok() {
                    new_rules.push((fixed_ex1.clone(), fixed_ex2.clone(), rw.unwrap()));
                } else {
                    println!("Err creating rewrite, probably existential");
                    println!("{}", fixed_ex1.pretty(80) + " => " + &*fixed_ex2.pretty(80));
                }
            }
            if text2.starts_with("(") {
                let rw = Rewrite::new(text2.clone(), text2.clone(), fixed_ex2.clone(), fixed_ex1.clone());
                if rw.is_ok() {
                    new_rules.push((fixed_ex2.clone(), fixed_ex1.clone(), rw.unwrap()));
                } else {
                    println!("Err creating rewrite, probably existential");
                    println!("{}", fixed_ex2.pretty(80) + " => " + &*fixed_ex1.pretty(80));
                }
            }
            Some(new_rules)
        } else {
            None
        }
    }

    fn check_equality(rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> bool {
        let mut egraph = EGraph::default();
        egraph.add_expr(ex1);
        egraph.add_expr(ex2);
        egraph.rebuild();
        let runner = Runner::default().with_iter_limit(8).with_time_limit(Duration::from_secs(60)).with_node_limit(10000).with_egraph(egraph).run(rules);
        !runner.egraph.equivs(ex1, ex2).is_empty()
    }

    pub fn run(&mut self, rules: &mut Vec<Rewrite<SymbolLang, ()>>, max_depth: usize) -> Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)> {
        // TODO: case split
        // TODO: run full tests
        // TODO: 2 phs and generalize
        println!("Running TheSy on datatypes: {} dict: {}", self.datatypes.keys().map(|x| &x.name).join(" "), self.dict.iter().map(|x| &x.0).join(" "));

        let system_rws_start = rules.len();
        let mut found_rules = vec![];
        for r in self.apply_rws.iter().chain(self.ite_rws.iter()) {
            rules.push(r.clone());
        }
        let new_rules_index = rules.len();

        for depth in 0..max_depth {
            self.increase_depth();
            self.node_limit = match self.equiv_reduc(&rules[..]) {
                StopReason::NodeLimit(x) => {
                    println!("Reached node limit. Increasing maximum graph size.");
                    x + 100000
                }
                _ => { self.node_limit }
            };
            Self::case_split_all(rules, &mut self.egraph, 2, 4);

            let mut conjectures = self.get_conjectures();
            'outer: while !conjectures.is_empty() {
                let (key, ex1, ex2, d) = conjectures.pop().unwrap();
                let new_rules = self.prove(&rules[..], &d, &ex1, &ex2);
                if new_rules.is_some() {
                    if Self::check_equality(&rules[..], &ex1, &ex2) {
                        println!("bad conjecture {} = {}", &ex1.pretty(500), &ex2.pretty(500));
                        continue 'outer;
                    }
                    found_rules.extend_from_slice(&new_rules.as_ref().unwrap());
                    // TODO: move print out of prove
                    for r in new_rules.unwrap() {
                        println!("proved: {}", r.2.long_name());
                        // inserting like this so new rule will apply before running into node limit.
                        rules.insert(new_rules_index, r.2);
                    }
                    let reduc_depth = 3;
                    self.node_limit = match self.equiv_reduc_depth(&rules[..], reduc_depth) {
                        StopReason::NodeLimit(x) => {
                            println!("Reached node limit. Increasing maximum graph size.");
                            x + 100000
                        }
                        _ => { self.node_limit }
                    };
                    conjectures = self.get_conjectures();
                    println!();
                }
            }
        }
        for i in 0..self.apply_rws.len() {
            rules.remove(system_rws_start);
        }
        found_rules
    }
}

/// *** Thesy statics ***
impl TheSy {
    /// Appears at the start of every placeholder var
    const PH_START: &'static str = "ts_ph";
    /// To be used as the op of edges representing potential split
    const SPLITTER: &'static str = "potential_split";
    /// Pattern to find all available splitter edges. Limited arbitrarily to 5 possible splits.
    fn split_patterns() -> Vec<Pattern<SymbolLang>> {
        vec![
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1)", Self::SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2)", Self::SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2 ?c3)", Self::SPLITTER)).unwrap(),
            Pattern::from_str(&*format!("({} ?root ?c0 ?c1 ?c2 ?c3 ?c4)", Self::SPLITTER)).unwrap(),
        ]
    }

    /// Case splitting works by cloning the graph and merging the different possibilities.
    /// Enabling recursivly splitting all
    fn case_split(rules: &[Rewrite<SymbolLang, ()>], egraph: &mut EGraph<SymbolLang, ()>, root: Id, splits: Vec<Id>, split_depth: usize, run_depth: usize) {
        let classes = egraph.classes().collect_vec();
        // TODO: parallel
        let after_splits = splits.iter().map(|child| {
            let mut new_graph = egraph.clone();
            new_graph.union(root, *child);
            // TODO: graph limit enhancing runner, with rules sorting
            let mut runner = Runner::default().with_time_limit(Duration::from_secs(60 * 5)).with_node_limit(new_graph.total_number_of_nodes() + 200000).with_egraph(new_graph).with_iter_limit(run_depth);
            runner = runner.run(rules);
            runner.egraph.rebuild();
            Self::case_split_all(rules, &mut runner.egraph, split_depth - 1, run_depth);
            classes.iter().map(|c| (c.id, runner.egraph.find(c.id))).collect::<HashMap<Id, Id>>()
        }).collect_vec();
        let mut group_by_splits: HashMap<Vec<Id>, HashSet<Id>> = HashMap::new();
        for c in classes {
            let key = after_splits.iter().map(|m| m[&c.id]).collect_vec();
            if !group_by_splits.contains_key(&key) {
                group_by_splits.insert(key.clone(), HashSet::new());
            }
            group_by_splits.get_mut(&key).unwrap().insert(c.id);
        }
        for group in group_by_splits.values().filter(|g| g.len() > 1) {
            let first = group.iter().next().unwrap();
            for id in group.iter().dropping(1) {
                egraph.union(*first, *id);
            }
        }
        egraph.rebuild();
    }

    fn case_split_all(rules: &[Rewrite<SymbolLang, ()>], egraph: &mut EGraph<SymbolLang, ()>, split_depth: usize, run_depth: usize) {
        // TODO: marked used splitters to prevent reusing
        if split_depth == 0 {
            return;
        }
        println!("split depth {}", split_depth);
        let root_var: Var = "?root".parse().unwrap();
        let children_vars: Vec<Var> = (0..5).map(|i| format!("?c{}", i).parse().unwrap()).collect_vec();
        let splitters: Vec<(usize, Vec<Subst>)> = Self::split_patterns().iter().enumerate()
            .map(|(i, p)| {
                (i + 2, p.search(egraph).into_iter().flat_map(|x| x.substs).collect_vec())
            }).collect_vec();
        splitters.iter().for_each(|(child_count, substs)|
            {
                println!("substs for {} len {}", child_count, substs.len());
                substs.iter().for_each(|s| {
                    println!("split by {:#?}", *s.get(root_var).unwrap());
                    let params = (0..*child_count).map(|i| *s.get(children_vars[i]).unwrap()).collect_vec();
                    Self::case_split(rules, egraph, *s.get(root_var).unwrap(), params, split_depth, run_depth);
                })
            });
    }

    /// Create all needed phs from
    fn collect_phs(dict: &Vec<(String, RecExpr<SymbolLang>)>, ph_count: usize) -> Vec<(String, RecExpr<SymbolLang>)> {
        // TODO: only two phs of non recursive types
        let mut res = HashSet::new();
        for (name, typ) in dict {
            if typ.into_tree().root().op.to_string() == "->" {
                for e in typ.into_tree().children().iter().dropping_back(1) {
                    res.insert(e.into());
                }
            }
        }
        let mut phs = vec![];
        for d in res {
            for i in 0..ph_count {
                phs.push((Self::get_ph(&d, i), d.clone()));
            }
        }
        phs
    }

    fn wfo_op() -> &'static str { "ltwf" }

    fn wfo_trans() -> Rewrite<SymbolLang, ()> {
        let searcher = MultiDiffSearcher::new(vec![
            Pattern::from_str(&vec!["(", Self::wfo_op(), "?x ?y)"].join(" ")).unwrap(),
            Pattern::from_str(&vec!["(", Self::wfo_op(), "?z ?x)"].join(" ")).unwrap()]);
        let applier = Pattern::from_str(&vec!["(", Self::wfo_op(), "?z ?y)"].join(" ")).unwrap();
        Rewrite::new("wfo transitivity", "well founded order transitivity", searcher, applier).unwrap()
    }

    /// create well founded order rewrites for constructors of Datatype `datatype`.
    fn wfo_datatype(datatype: &DataType) -> Vec<Rewrite<SymbolLang, ()>> {
        // TODO: all buit values are bigger then base values
        let contructor_rules = datatype.constructors.iter()
            .filter(|c| !c.params.is_empty())
            .flat_map(|c| {
                let params = c.params.iter().enumerate()
                    .map(|(i, t)|
                        (format!("?param_{}", i).to_string(), *t == datatype.as_exp())
                    ).collect_vec();
                let contr_pattern = Pattern::from_str(&*format!("({} {})", c.name, params.iter().map(|s| s.0.clone()).intersperse(" ".to_string()).collect::<String>())).unwrap();
                let searcher = MultiEqSearcher::new(vec![
                    contr_pattern,
                    Pattern::from_str("?root").unwrap(),
                ]);

                let appliers = params.iter()
                    .filter(|x| x.1)
                    .map(|x| (x.0.clone(), DiffApplier::new(
                        Pattern::from_str(&*format!("({} {} ?root)", Self::wfo_op(), x.0)).unwrap()
                    )));

                // rules
                appliers.map(|a| {
                    Rewrite::new(format!("{}_{}", c.name, a.0), format!("{}_{}", c.name, a.0), searcher.clone(), a.1).unwrap()
                }).collect_vec()
            });
        let mut res = contructor_rules.collect_vec();
        res.push(Self::wfo_trans());
        res
    }

    fn get_ph(d: &RecExpr<SymbolLang>, i: usize) -> String {
        let s = d.into_tree().to_spaceless_string();
        let res = format!("{}_{}_{}", Self::PH_START, s, i);
        res
    }

    fn get_ind_var(d: &DataType) -> String {
        Self::get_ph(&d.as_exp(), 0)
    }

    fn ident_mapper(i: &String, induction_ph: &String, sub_ind: &String) -> String {
        if i == induction_ph {
            sub_ind.clone()
        } else if i.starts_with(TheSy::PH_START) {
            format!("?{}", i)
        } else {
            i.clone()
        }
    }

    fn clean_vars(i: String) -> String {
        if i.starts_with("?") {
            i[1..].to_string()
        } else { i }
    }

    fn create_hypothesis(induction_ph: &String, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Vec<Rewrite<SymbolLang, ()>> {
        assert!(!induction_ph.starts_with("?"));
        // used somevar but wasnt recognised as var
        let ind_replacer = "?somevar".to_string();
        let clean_term1 = Self::pattern_from_exp(ex1, induction_ph, &ind_replacer);
        let clean_term2 = Self::pattern_from_exp(ex2, induction_ph, &ind_replacer);
        let pret = clean_term1.pretty(500);
        let pret2 = clean_term2.pretty(500);
        let precondition = Pattern::from_str(&*format!("({} {} {})", Self::wfo_op(), ind_replacer, induction_ph)).unwrap();
        let precond_pret = precondition.pretty(500);
        let mut res = vec![];
        // Precondition on each direction of the hypothesis
        if pret.starts_with("(") {
            let rw = Rewrite::new("IH1", "IH1", MultiDiffSearcher::new(vec![clean_term1.clone(), precondition.clone()]), clean_term2.clone());
            if rw.is_ok() {
                res.push(rw.unwrap())
            } else {
                println!("Failed to add rw, probably existential");
                println!("{} |> {} => {}", precond_pret, pret, pret2);
            }
        }
        if pret2.starts_with("(") {
            let rw = Rewrite::new("IH2", "IH2", MultiDiffSearcher::new(vec![clean_term2.clone(), precondition.clone()]), clean_term1.clone());
            if rw.is_ok() {
                res.push(rw.unwrap())
            } else {
                println!("Failed to add rw, probably existential");
                println!("{} |> {} => {}", precond_pret, pret2, pret);
            }
        }
        res
    }

    fn pattern_from_exp(exp: &RecExpr<SymbolLang>, induction_ph: &String, sub_ind: &String) -> Pattern<SymbolLang> {
        let mapped = exp.as_ref().iter().cloned().map(|mut n| {
            n.op = Self::ident_mapper(&n.op.to_string(), induction_ph, sub_ind).parse().unwrap();
            n
        }).collect_vec();
        Pattern::from_str(&*RecExpr::from(mapped).pretty(500)).unwrap()
    }
}

#[cfg(test)]
mod test {
    use crate::thesy::{TheSy, DataType};
    use crate::tree::Tree;
    use std::rc::Rc;
    use std::str::FromStr;
    use std::time::SystemTime;
    use itertools::Itertools;
    use std::collections::HashSet;
    use egg::{SymbolLang, Pattern, Searcher, Rewrite, RecExpr, EGraph, Runner};

    fn create_nat_type() -> DataType {
        DataType::new("nat".to_string(), vec![
            "(Z nat)".parse().unwrap(),
            "(S nat nat)".parse().unwrap()
        ])
    }

    fn create_list_type() -> DataType {
        DataType::new("list".to_string(), vec![
            "(Nil list)".parse().unwrap(),
            "(Cons nat list list)".parse().unwrap()
        ])
    }

    fn create_nat_sygue() -> TheSy {
        TheSy::new(
            create_nat_type(),
            vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| s.parse().unwrap()).collect(),
            vec![("Z".to_string(), "nat".parse().unwrap()), ("S".to_string(), "(-> nat nat)".parse().unwrap()), ("pl".to_string(), "(-> nat nat nat)".parse().unwrap())],
        )
    }

    fn create_list_sygue() -> TheSy {
        TheSy::new(
            create_list_type(),
            vec!["Nil".parse().unwrap(), "(Cons x Nil)".parse().unwrap(), "(Cons y (Cons x Nil))".parse().unwrap()],
            vec![("Nil", "list"), ("Cons", "(-> nat list list)"), ("snoc", "(-> list nat list)"), ("rev", "(-> list list)"), ("app", "(-> list list list)")].into_iter()
                .map(|(name, typ)| (name.to_string(), RecExpr::from_str(typ).unwrap())).collect(),
        )
    }

    fn create_pl_rewrites() -> Vec<Rewrite<SymbolLang, ()>> {
        vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")]
    }

    fn create_list_rewrites() -> Vec<Rewrite<SymbolLang, ()>> {
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
        let start = SystemTime::now();
        syg.increase_depth();
        syg.increase_depth();
        let level0 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() == 0)
            .map(|c| (c.id, c.nodes[0].clone()))
            .collect_vec();
        let edges_level0 = level0.iter().map(|c| &c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level0.len(), level0.len());
        let level1 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level1 = level1.iter().map(|c| c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level1.len(), level1.len());
        let level2 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.iter().any(|n| level1.iter().find(|x| x.0 == *n).is_some()))
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some() || level1.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level2 = level2.iter().map(|c| c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level2.len(), level2.len());
    }

    #[test]
    fn test_creates_expected_terms_nat() {
        let mut syg = create_nat_sygue();
        let nat = create_nat_type();
        let z = syg.egraph.lookup(SymbolLang::new("Z", vec![]));
        assert!(z.is_some());
        let sz = syg.egraph.lookup(SymbolLang::new("S", vec![z.unwrap()]));
        assert!(sz.is_some());
        let ssz = syg.egraph.lookup(SymbolLang::new("S", vec![sz.unwrap()]));
        assert!(ssz.is_some());
        let ind_ph = syg.egraph.lookup(SymbolLang::new(TheSy::get_ind_var(&nat), vec![]));
        assert!(ind_ph.is_some());
        let ph1 = syg.egraph.lookup(SymbolLang::new(TheSy::get_ph(&nat.as_exp(), 1), vec![]));
        assert!(ph1.is_some());
        let ph2 = syg.egraph.lookup(SymbolLang::new(TheSy::get_ph(&nat.as_exp(), 2), vec![]));
        assert!(ph2.is_some());
        syg.increase_depth();
        let pl_ph1_ex2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ph1.unwrap()), syg.egraph.find(ssz.unwrap())]));
        assert!(pl_ph1_ex2.is_some());
        let pl_ind_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ind_ph.unwrap()), syg.egraph.find(ph2.unwrap())]));
        assert!(pl_ind_ph2.is_some());
        let s_ph2 = syg.egraph.lookup(SymbolLang::new("S", vec![syg.egraph.find(ph2.unwrap())]));
        assert!(s_ph2.is_some());
        syg.increase_depth();
        let pl_pl_ph1_ex2_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(pl_ph1_ex2.unwrap()), syg.egraph.find(ssz.unwrap())]));
        assert!(pl_pl_ph1_ex2_ph2.is_some());
    }

    #[test]
    fn does_not_create_unneeded_terms() {
        let mut syg = TheSy::new_with_ph(
            vec![create_nat_type()],
            vec!["Z"].into_iter().map(|s| s.parse().unwrap()).collect(),
            vec![("S".to_string(), "(-> nat nat)".parse().unwrap())],
            2,
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(typed ?x ?y)").unwrap();
        let results0 = anchor_patt.search(&syg.egraph);
        assert_eq!(2usize, results0.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(4usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(6usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());

        let mut syg = TheSy::new_with_ph(
            // For this test dont use full definition
            vec![DataType::new("nat".to_string(), vec![
                "(Z nat)".parse().unwrap(),
                // Tree::from_str("(S nat nat)").unwrap()
            ])],
            vec!["Z"].into_iter().map(|s| s.parse().unwrap()).collect(),
            vec![("x".to_string(), "(-> nat nat nat)".parse().unwrap())],
            3,
        );

        let results0 = anchor_patt.search(&syg.egraph);
        assert_eq!(3usize, results0.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        let results1 = anchor_patt.search(&syg.egraph);
        assert_eq!(12usize, results1.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        let results2 = anchor_patt.search(&syg.egraph);
        assert_eq!(147usize, results2.iter().map(|x| x.substs.len()).sum());
    }

    #[test]
    fn check_representatives_sane() {
        let mut syg = create_nat_sygue();
        let mut rewrites = create_pl_rewrites();

        syg.increase_depth();
        syg.equiv_reduc(&rewrites);
        syg.increase_depth();
        syg.equiv_reduc(&rewrites);
        let classes = syg.extract_classes();
        for (id, (ord, exp)) in classes {
            for n in exp.as_ref() {
                if n.op.to_string() == "pl" {
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
        syg.equiv_reduc(&rewrites);
        syg.increase_depth();
        syg.equiv_reduc(&rewrites);
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
    fn wfo_trans_ok() {
        let mut egraph = EGraph::default();
        egraph.add_expr("(ltwf x y)".parse().as_ref().unwrap());
        egraph.add_expr("(ltwf y z)".parse().as_ref().unwrap());
        egraph = Runner::default().with_egraph(egraph).run(&vec![TheSy::wfo_trans()][..]).egraph;
        let pat: Pattern<SymbolLang> = "(ltwf x z)".parse().unwrap();
        assert!(pat.search(&egraph).iter().all(|s| !s.substs.is_empty()));
        assert!(!pat.search(&egraph).is_empty());
    }

    #[test]
    fn wfo_nat_ok() {
        let mut egraph = EGraph::default();
        egraph.add_expr("(S y)".parse().as_ref().unwrap());
        egraph = Runner::default().with_egraph(egraph).run(&TheSy::wfo_datatype(&create_nat_type())[..]).egraph;
        let pat: Pattern<SymbolLang> = "(ltwf y (S y))".parse().unwrap();
        assert!(pat.search(&egraph).iter().all(|s| !s.substs.is_empty()));
        assert!(!pat.search(&egraph).is_empty());
    }

    #[test]
    fn prove_pl_zero() {
        let mut syg = create_nat_sygue();
        let nat = create_nat_type();
        let mut rewrites = create_pl_rewrites();
        let ind_rec = TheSy::get_ind_var(&nat);
        assert!(syg.prove(&rewrites[..], &nat, &format!("(pl {} Z)", ind_rec).parse().unwrap(), &ind_rec.parse().unwrap()).is_some())
    }

    // TODO: test on lists
}