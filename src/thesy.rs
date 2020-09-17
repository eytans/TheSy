use std::rc::Rc;
use crate::tree::Tree;
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

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct DataType {
    name: String,
    type_params: Vec<Tree>,
    /// Constructor name applied on types
    constructors: Vec<Tree>,
}

impl DataType {
    pub(crate) fn new(name: String, constructors: Vec<Tree>) -> DataType {
        DataType { name, type_params: vec![], constructors }
    }

    fn generic(name: String, type_params: Vec<Tree>, constructors: Vec<Tree>) -> DataType {
        DataType { name, type_params, constructors }
    }

    fn as_tree(&self) -> Tree {
        Tree::branch(self.name.clone(), self.type_params.iter().map(|t| Rc::new(t.clone())).collect_vec())
    }
}

pub struct TheSy {
    // TODO: automatic examples
    examples: Vec<Rc<Tree>>,
    // TODO: datatype out of dict, multiple examples at once
    /// known datatypes to wfo rewrites for induction
    datatypes: HashMap<DataType, Vec<Rewrite<SymbolLang, ()>>>,
    /// known function declerations and their types
    dict: Vec<Rc<Tree>>,
    /// name used to mark where the induction will be
    ind_ph: Rc<Tree>,
    /// egraph which is expanded as part of the exploration
    pub egraph: EGraph<SymbolLang, ()>,
    /// searchers used to create the next depth of terms
    searchers: HashMap<String, (MultiDiffSearcher, Vec<Var>)>,
    /// map maintaining the connection between eclasses created by sygue
    /// and their associated eclasses with `ind_ph` replaced by symbolic examples.
    example_ids: HashMap<Id, Vec<Id>>,
}

// TODO: use conditional search\applier where applicable
/// Thesy
impl TheSy {
    const PH_START: &'static str = "ts_ph";

    fn wfo_op() -> &'static str { "ltwf" }

    fn wfo_trans() -> Rewrite<SymbolLang, ()>  {
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
            .filter(|c| c.subtrees.len() > 1)
            .flat_map(|c| {
                let params = c.subtrees.iter()
                    .take(c.subtrees.len() - 1).enumerate()
                    .map(|(i, t)|
                        (format!("?param_{}", i).to_string(), **t == datatype.as_tree())
                    ).collect_vec();
                let contr_pattern = Pattern::from_str(&*format!("({} {})", c.root, params.iter().map(|s| s.0.clone()).intersperse(" ".to_string()).collect::<String>())).unwrap();
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
                    Rewrite::new(format!("{}_{}", c.root, a.0), format!("{}_{}", c.root, a.0), searcher.clone(), a.1).unwrap()
                }).collect_vec()
            });
        let mut res = contructor_rules.collect_vec();
        res.push(Self::wfo_trans());
        res
    }

    // TODO: ind from example types
    pub fn new(datatypes: Vec<DataType>, examples: Vec<Rc<Tree>>, dict: Vec<Rc<Tree>>) -> TheSy {
        let datatype_to_wfo = datatypes.into_iter()
            .map(|d| (d.clone(), Self::wfo_datatype(&d))).collect();

        let ind_ph = Rc::new(Tree::tleaf(String::from("ind_var"), Rc::new(Some(Tree::leaf(String::from("nat"))))));
        let mut egraph = EGraph::default();
        let anchor = Self::create_sygue_anchor();
        let mut example_ids = HashMap::new();
        let ind_id = ind_ph.add_to_graph(&mut egraph);
        egraph.add(SymbolLang::new(anchor.clone(), vec![ind_id]));
        let initial_example_ids = examples.iter()
            .map(|e| e.add_to_graph(&mut egraph)).collect_vec();
        example_ids.insert(ind_id, initial_example_ids);
        for v in dict.iter().filter(|v| v.subtrees[1].is_leaf()) {
            let id = v.subtrees[0].add_to_graph(&mut egraph);
            egraph.add(SymbolLang::new(anchor.clone(), vec![id]));
            example_ids.insert(id, Vec::from_iter(iter::repeat(id).take(examples.len())));
        }

        let mut res = TheSy {
            examples,
            datatypes: datatype_to_wfo,
            dict,
            ind_ph,
            egraph,
            // sygue_rules: vec![],
            searchers: HashMap::new(),
            example_ids,
        };

        res.searchers = res.create_sygue_serchers();
        res.egraph.rebuild();
        res
    }

    fn extract_classes(&self) -> HashMap<Id, (RepOrder, RecExpr<SymbolLang>)> {
        let mut ext = Extractor::new(&self.egraph, MinRep);
        // TODO: update example ids as whole
        self.example_ids.keys().map(|key| {
            let updated_key = &self.egraph.find(*key);
            (*updated_key, ext.find_best(*updated_key))
        }).collect()
    }

    fn create_sygue_anchor() -> String {
        format!("sygueanchor")
    }

    fn create_sygue_serchers(&self) -> HashMap<String, (MultiDiffSearcher, Vec<Var>)> {
        let mut res = HashMap::new();
        self.dict.iter().for_each(|f| {
            assert_eq!(f.root, "typed");
            let fun_name = &f.subtrees[0].root;
            let fun_type = &f.subtrees[1];
            if fun_type.root == "->" {
                let params: Vec<Var> = (0..fun_type.subtrees.len() - 1).map(|i| Var::from_str(&*format!("?param_{}", i)).unwrap()).collect_vec();
                let anchor = TheSy::create_sygue_anchor();
                let patterns = fun_type.subtrees.iter().take(fun_type.subtrees.len() - 1).enumerate()
                    .flat_map(|(i, t)| {
                        let pat_string = format!("({} ?param_{})", anchor, i);
                        vec![
                            Pattern::from_str(&*pat_string).unwrap(),
                            // Pattern::from_str(&*format!("(typed ?param_{} {})", i, t.to_string())).unwrap(),
                        ]
                    }).collect::<Vec<Pattern<SymbolLang>>>();
                res.insert(fun_name.clone(), (MultiDiffSearcher::new(patterns), params));
            }
        });
        res
    }

    fn fix_example_ids(&mut self) {
        self.example_ids = self.example_ids.iter()
            .map(|(k, v)| (self.egraph.find(*k), v.iter().map(|x| self.egraph.find(*x)).collect())).collect();
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
        let anchor = Self::create_sygue_anchor();
        fn create_edge(op: &String, params: &Vec<Var>, sub: &Subst) -> SymbolLang {
            SymbolLang::new(op.clone(), params.iter().map(|v| sub.get(v.clone()).unwrap()).copied().collect())
        }

        fn translate_edge(edge: &SymbolLang, e_index: usize, translations: &HashMap<Id, Vec<Id>>) -> SymbolLang {
            let new_child = edge.children.iter().map(|id| {
                translations[id][e_index]
            }).collect_vec();
            SymbolLang::new(edge.op.clone(), new_child)
        }
        let length = self.examples.len();

        let op_matches = self.searchers.iter()
            .map(|(op, (searcher, params))| {
                (op, params, searcher.search(&self.egraph).iter_mut().flat_map(|mut sm| std::mem::take(&mut sm.substs)).collect_vec())
            }).collect_vec();
        for (op, params, subs) in op_matches {
            for sub in subs {
                // Foreach match add a term for ind_ph and foreach example and update example_ids map
                let new_edge = create_edge(op, params, &sub);
                let key = self.egraph.add(new_edge.clone());
                self.egraph.add(SymbolLang::new(anchor.clone(), vec![key]));
                let mut new_ids = vec![];
                for i in 0..length {
                    new_ids.push(self.egraph.add(translate_edge(&new_edge, i, &self.example_ids)));
                }
                self.example_ids.insert(key, new_ids);
            }
        }
        self.egraph.rebuild();
    }

    pub fn equiv_reduc(&mut self, rules: &[Rewrite<SymbolLang, ()>]) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(8).run(rules).egraph;
        self.egraph.rebuild();
    }

    /// For all created terms, get possible equality conjectures.
    /// Uses equivalence classes created by equiv_reduc, and finds classes that
    /// are equal for examples but not for ind_var.
    /// Each such class (e.g. fine class) is represented using a single minimal term.
    /// return the conjectures ordered by representative size.
    pub fn get_conjectures(&mut self) -> Vec<(RepOrder, RecExpr<SymbolLang>, RecExpr<SymbolLang>)> {
        self.fix_example_ids();
        let mut finer_equality_classes: HashMap<Vec<Id>, HashSet<Id>> = HashMap::new();
        for (id, vals) in &self.example_ids {
            if !finer_equality_classes.contains_key(vals) {
                finer_equality_classes.insert(vals.iter().map(|i| self.egraph.find(*i)).collect_vec(), HashSet::new());
            }
            finer_equality_classes.get_mut(vals).expect("Should have just added if missing").insert(self.egraph.find(*id));
        }
        let reps = self.extract_classes();
        let mut res = Vec::new();
        for set in finer_equality_classes.values() {
            if set.len() < 2 { continue; }
            for couple in choose(&set.iter().collect_vec()[..], 2) {
                let min = if reps[couple[0]].0 <= reps[couple[1]].0 { reps[couple[0]].0.clone() }
                            else {reps[couple[1]].0.clone()};
                res.push((min, reps[couple[0]].1.clone(), reps[couple[1]].1.clone()));
            }
        }
        res.sort_by_key(|x| x.0.clone());
        res
    }

    fn ident_mapper(i: &String, induction_ph: &String, sub_ind: &String) -> String {
        if i == induction_ph {
            sub_ind.clone()
        }
        else if i.starts_with(TheSy::PH_START) {
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
        let mut res = vec![];
        // Precondition on each direction of the hypothesis
        if clean_term1.pretty(80).starts_with("(") {
            res.push(Rewrite::new("IH1", "IH1", MultiDiffSearcher::new(vec![clean_term1.clone(), precondition.clone()]), clean_term2.clone()).unwrap());
        }
        if clean_term2.pretty(80).starts_with("(") {
            res.push(Rewrite::new("IH2", "IH2", MultiDiffSearcher::new(vec![clean_term2, precondition]), clean_term1).unwrap());
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

    /// Assume base case is correct and prove equality using induction.
    /// Induction hypothesis is given as a rewrite rule, using precompiled rewrite rules
    /// representing well founded order on the induction variable.
    /// Need to replace the induction variable with an expression representing a constructor and
    /// well founded order on the params of the constructor.
    pub fn prove(&self, rules: &[Rewrite<SymbolLang, ()>], datatype: &DataType, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Option<Vec<Rewrite<SymbolLang, ()>>> {
        debug_assert!(ex1.as_ref().iter().find(|s| s.op.to_string() == self.ind_ph.root).is_some());
        debug_assert!(ex2.as_ref().iter().find(|s| s.op.to_string() == self.ind_ph.root).is_some());
        // rewrites to encode proof
        let mut rule_set = Self::create_hypothesis(&self.ind_ph.root, &ex1, &ex2);
        let wfo_rws = self.datatypes.get(&datatype).unwrap();
        rule_set.extend(rules.iter().cloned());
        rule_set.extend(wfo_rws.iter().cloned());
        // create graph containing both expressions
        let mut orig_egraph: EGraph<SymbolLang, ()> = EGraph::default();
        let ex1_id = orig_egraph.add_expr(&ex1);
        let ex2_id = orig_egraph.add_expr(&ex2);
        let ind_id = orig_egraph.lookup(SymbolLang::new(&self.ind_ph.root, vec![])).unwrap();
        let mut res = true;
        for c in datatype.constructors.iter().filter(|c| c.subtrees.len() > 1) {
            let mut egraph = orig_egraph.clone();
            let contr_exp = RecExpr::from_str(format!("({} {})", c.root, c.subtrees.iter().take(c.subtrees.len() - 1).enumerate()
                .map(|(i, t)| "param_".to_owned() + &*i.to_string())
                .intersperse(" ".parse().unwrap()).collect::<String>()).as_str()).unwrap();
            let contr_id = egraph.add_expr(&contr_exp);
            egraph.union(contr_id, ind_id);
            let mut runner: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).with_iter_limit(8).run(&rule_set[..]);
            res = res && !runner.egraph.equivs(&ex1, &ex2).is_empty()
        }
        if res {
            let fixed_ex1 = Self::pattern_from_exp(ex1, &self.ind_ph.root, &("?".to_owned() + &self.ind_ph.root));
            let fixed_ex2 = Self::pattern_from_exp(ex2, &self.ind_ph.root, &("?".to_owned() + &self.ind_ph.root));
            let text1 = fixed_ex1.pretty(80) + " = " + &*fixed_ex2.pretty(80);
            let text2 = fixed_ex2.pretty(80) + " = " + &*fixed_ex1.pretty(80);
            let mut new_rules = vec![];
            println!("proved: {}", text1);
            // TODO: dont do it so half assed
            if text1.starts_with("(") {
                new_rules.push(Rewrite::new(text1.clone(), text1, fixed_ex1.clone(), fixed_ex2.clone()).unwrap());
            }
            if text2.starts_with("(") {
                new_rules.push(Rewrite::new(text2.clone(), text2, fixed_ex2, fixed_ex1).unwrap());
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
        let runner = Runner::default().with_iter_limit(8).with_egraph(egraph).run(rules);
        !runner.egraph.equivs(ex1, ex2).is_empty()
    }

    pub fn run(&mut self, rules: &mut Vec<Rewrite<SymbolLang, ()>>, depth: usize) {
        let mut proved = false;
        for i in 0..depth {
            if proved {
                self.equiv_reduc(&rules[..]);
            }
            proved = false;
            self.increase_depth();
            self.equiv_reduc(&rules[..]);
            for (key, ex1, ex2) in self.get_conjectures() {
                if !Self::check_equality(&rules[..], &ex1, &ex2) {
                    for d in self.datatypes.keys() {
                        let new_rules = self.prove(&rules[..], d, &ex1, &ex2);
                        if new_rules.is_some() {
                            proved = true;
                            for r in new_rules.unwrap() {
                                println!("{}", r.long_name());
                                rules.push(r);
                            }
                        }
                    }
                }
            }
        }
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
            Tree::from_str("(Z nat)").unwrap(),
            Tree::from_str("(S nat nat)").unwrap()
        ])
    }

    fn create_nat_sygue() -> TheSy {
        TheSy::new(
            vec![create_nat_type()],
            vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ts_ph0 nat)", "(typed ts_ph1 nat)", "(typed Z nat)", "(typed S (-> nat nat))", "(typed pl (-> nat nat nat))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        )
    }

    fn create_pl_rewrites() -> Vec<Rewrite<SymbolLang, ()>> {
        vec![rewrite!("pl base"; "(pl Z ?x)" => "?x"), rewrite!("pl ind"; "(pl (S ?y) ?x)" => "(S (pl ?y ?x))")]
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
        let z = syg.egraph.lookup(SymbolLang::new("Z", vec![]));
        assert!(z.is_some());
        let sz = syg.egraph.lookup(SymbolLang::new("S", vec![z.unwrap()]));
        assert!(sz.is_some());
        let ssz = syg.egraph.lookup(SymbolLang::new("S", vec![sz.unwrap()]));
        assert!(ssz.is_some());
        let ind_ph = syg.egraph.lookup(SymbolLang::new(syg.ind_ph.root.clone(), vec![]));
        assert!(ind_ph.is_some());
        let ph1 = syg.egraph.lookup(SymbolLang::new("ts_ph0", vec![]));
        assert!(ph1.is_some());
        let ph2 = syg.egraph.lookup(SymbolLang::new("ts_ph1", vec![]));
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
        let mut syg = TheSy::new(
            vec![DataType::new("nat".to_string(), vec![
                Tree::from_str("(Z nat)").unwrap(),
                Tree::from_str("(S nat nat)").unwrap()
            ])],
            vec!["Z"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ts_ph0 nat)", "(typed S (-> nat nat))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(sygueanchor ?x)").unwrap();
        let results0 = anchor_patt.search(&syg.egraph);
        assert_eq!(2usize, results0.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(4usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(6usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());

        let mut syg = TheSy::new(
            // For this test dont use full definition
            vec![DataType::new("nat".to_string(), vec![
                Tree::from_str("(Z nat)").unwrap(),
                // Tree::from_str("(S nat nat)").unwrap()
            ])],
            vec!["Z"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ts_ph0 nat)", "(typed ts_ph1 nat)", "(typed x (-> nat nat nat))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(sygueanchor ?x)").unwrap();
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
        assert!(syg.prove(&rewrites[..], nat, format!("(pl {} Z)", syg.ind_ph.root).parse().unwrap(), syg.ind_ph.root.parse().unwrap()).is_some())
    }

    // TODO: test on lists
}