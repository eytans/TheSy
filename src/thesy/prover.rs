use crate::lang::{DataType, Function};
use egg::{Rewrite, SymbolLang, Pattern, EGraph, RecExpr, Runner, ENodeOrVar, Var, Id, PatternAst};
use crate::eggstentions::multisearcher::multisearcher::{MultiDiffSearcher, MultiEqSearcher};
use std::str::FromStr;
use itertools::Itertools;
use crate::eggstentions::appliers::DiffApplier;
use crate::thesy::TheSy;
use crate::eggstentions::expression_ops::{RecExpSlice, IntoTree, Tree};

pub struct Prover {
    datatype: DataType,
    wfo_rules: Vec<Rewrite<SymbolLang, ()>>
}

impl Prover {
    pub fn new(datatype: DataType) -> Prover {
        let wfo_rules = Self::wfo_datatype(&datatype);
        Prover{datatype, wfo_rules}
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

    // TODO: write this function and allow only 2 phs.
    // pub fn generalize_prove(&self, rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Option<Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
    //     fn collect_ph1_indexes()
    // }

    /// Assume base case is correct and prove equality using induction.
   /// Induction hypothesis is given as a rewrite rule, using precompiled rewrite rules
   /// representing well founded order on the induction variable.
   /// Need to replace the induction variable with an expression representing a constructor and
   /// well founded order on the params of the constructor.
    pub fn prove(&self, rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Option<Vec<(Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        if ex1.as_ref().iter().find(|s| s.op.to_string() == TheSy::get_ind_var(&self.datatype).name).is_none() &&
            ex2.as_ref().iter().find(|s| s.op.to_string() == TheSy::get_ind_var(&self.datatype).name).is_none() {
            return None;
        }
        // rewrites to encode proof
        let mut rule_set = Self::create_hypothesis(&TheSy::get_ind_var(&self.datatype), &ex1, &ex2);
        let wfo_rws = &self.wfo_rules;
        rule_set.extend(rules.iter().cloned());
        rule_set.extend(wfo_rws.iter().cloned());
        // create graph containing both expressions
        let mut orig_egraph: EGraph<SymbolLang, ()> = EGraph::default();
        let ex1_id = orig_egraph.add_expr(&ex1);
        let ex2_id = orig_egraph.add_expr(&ex2);
        let ind_id = orig_egraph.lookup(SymbolLang::new(&TheSy::get_ind_var(&self.datatype).name, vec![])).unwrap();
        let mut res = true;
        for c in self.datatype.constructors.iter().filter(|c| !c.params.is_empty()) {
            let mut egraph = orig_egraph.clone();
            let contr_exp = RecExpr::from_str(format!("({} {})", c.name, c.params.iter().enumerate()
                .map(|(i, t)| "param_".to_owned() + &*i.to_string())
                .intersperse(" ".parse().unwrap()).collect::<String>()).as_str()).unwrap();
            let contr_id = egraph.add_expr(&contr_exp);
            egraph.union(contr_id, ind_id);
            let mut runner: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).with_iter_limit(8).run(&rule_set[..]);
            TheSy::case_split_all(&rule_set, &mut runner.egraph, 2, 4);
            res = res && !runner.egraph.equivs(&ex1, &ex2).is_empty()
        }
        if res {
            let fixed_ex1 = Self::pattern_from_exp(ex1, &TheSy::get_ind_var(&self.datatype), &("?".to_owned() + &TheSy::get_ind_var(&self.datatype).name));
            let fixed_ex2 = Self::pattern_from_exp(ex2, &TheSy::get_ind_var(&self.datatype), &("?".to_owned() + &TheSy::get_ind_var(&self.datatype).name));
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

    fn create_hypothesis(induction_ph: &Function, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Vec<Rewrite<SymbolLang, ()>> {
        assert!(!induction_ph.name.starts_with("?"));
        // used somevar but wasnt recognised as var
        let ind_replacer = "?somevar".to_string();
        let clean_term1 = Self::pattern_from_exp(ex1, induction_ph, &ind_replacer);
        let clean_term2 = Self::pattern_from_exp(ex2, induction_ph, &ind_replacer);
        let pret = clean_term1.pretty(500);
        let pret2 = clean_term2.pretty(500);
        let precondition = Pattern::from_str(&*format!("({} {} {})", Self::wfo_op(), ind_replacer, induction_ph.name)).unwrap();
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

    fn pattern_from_exp(exp: &RecExpr<SymbolLang>, induction_ph: &Function, sub_ind: &String) -> Pattern<SymbolLang> {
        let mut res_exp: RecExpr<ENodeOrVar<SymbolLang>> = RecExpr::default();
        fn add_to_exp(res: &mut RecExpr<ENodeOrVar<SymbolLang>>, inp: &RecExpSlice<SymbolLang>, induction_ph: &String, sub_ind: &String) -> Id {
            let mut ids = inp.children().iter().map(|c| add_to_exp(res, c, induction_ph, sub_ind)).collect_vec();
            let mut root = inp.root().clone();
            root.op = Prover::ident_mapper(&root.op.to_string(), induction_ph, sub_ind).parse().unwrap();
            let is_var = root.op.to_string().starts_with("?");
            if (!ids.is_empty()) && is_var {
                // Special case of vairable function
                let func_id = res.add(ENodeOrVar::ENode(SymbolLang::new(root.op.to_string(), vec![])));
                ids.insert(0, func_id);
                res.add(ENodeOrVar::ENode(SymbolLang::new("apply", ids)))
            } else if is_var {
                res.add(ENodeOrVar::Var(Var::from_str(&*root.op.to_string()).unwrap()))
            } else {
                res.add(ENodeOrVar::ENode(root.clone()))
            }
        }
        add_to_exp(&mut res_exp, &exp.into_tree(), &induction_ph.name, sub_ind);
        Pattern::from(PatternAst::from(res_exp))
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
}