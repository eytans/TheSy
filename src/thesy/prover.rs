use std::cmp::max;
use std::str::FromStr;

use egg::{EGraph, ENodeOrVar, Id, Language, Pattern, RecExpr, Rewrite, Runner, Symbol, SymbolLang, Var};
use itertools::Itertools;
use log::{debug, info};
use permutohedron::control::Control;
use permutohedron::heap_recursive;

use crate::eggstentions::appliers::DiffApplier;
use crate::eggstentions::expression_ops::{IntoTree, RecExpSlice, Tree};
use crate::eggstentions::searchers::multisearcher::{EitherSearcher, MultiDiffSearcher, MultiEqSearcher};
use crate::eggstentions::pretty_string::PrettyString;
use crate::lang::{DataType, Function};
use crate::thesy::TheSy;
use crate::thesy::case_split::CaseSplit;

pub struct Prover {
    datatype: DataType,
    wfo_rules: Vec<Rewrite<SymbolLang, ()>>,
    ind_var: Function,
}

impl Prover {
    const CASE_SPLIT_DEPTH: usize = 2;
    const CASE_SPLIT_RUN: usize = 4;
    const RUN_DEPTH: usize = 12;

    pub fn new(datatype: DataType) -> Prover {
        let wfo_rules = Self::wfo_datatype(&datatype);
        let ind_var = TheSy::get_ind_var(&datatype);
        Prover { datatype, wfo_rules, ind_var }
    }

    fn wfo_op() -> &'static str { "ltwf" }

    fn wfo_trans() -> Rewrite<SymbolLang, ()> {
        let searcher = MultiDiffSearcher::new(vec![
            Pattern::from_str(&*format!("({} ?z ?x)", Self::wfo_op())).unwrap(),
            Pattern::from_str(&*format!("({} ?x ?y)", Self::wfo_op())).unwrap()]);
        let applier = Pattern::from_str(&*format!("({} ?z ?y)", Self::wfo_op())).unwrap();
        Rewrite::new("wfo transitivity", searcher, applier).unwrap()
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
                    Rewrite::new(format!("{}_{}", c.name, a.0), searcher.clone(), a.1).unwrap()
                }).collect_vec()
            });
        let mut res = contructor_rules.collect_vec();
        res.push(Self::wfo_trans());
        res
    }

    fn not_containing_ind_var(&self, ex: &RecExpr<SymbolLang>) -> bool {
        ex.as_ref().iter().find(|s| s.op.to_string() == self.ind_var.name).is_none()
    }

    pub fn create_graph(precond: Option<&RecExpr<SymbolLang>>, ex1: &&RecExpr<SymbolLang>, ex2: &&RecExpr<SymbolLang>) -> EGraph<SymbolLang, ()> {
        let mut orig_egraph: EGraph<SymbolLang, ()> = EGraph::default();
        let _ = orig_egraph.add_expr(&ex1);
        let _ = orig_egraph.add_expr(&ex2);
        if precond.is_some() {
            let precond_id = orig_egraph.add_expr(precond.unwrap());
            let true_id = orig_egraph.add_expr(&RecExpr::from_str("true").unwrap());
            orig_egraph.union(precond_id, true_id);
            orig_egraph.add(SymbolLang::new("=", vec![precond_id, true_id]));
        }
        orig_egraph.rebuild();
        orig_egraph
    }

    fn create_proof_graph(&self, precond: Option<&RecExpr<SymbolLang>>, ex1: &&RecExpr<SymbolLang>, ex2: &&RecExpr<SymbolLang>) -> (EGraph<SymbolLang, ()>, Id) {
        let orig_egraph = Self::create_graph(precond, ex1, ex2);
        let ind_id = orig_egraph.lookup(SymbolLang::new(&self.ind_var.name, vec![])).unwrap();
        (orig_egraph, ind_id)
    }

    fn replace_at_indexes(ex: &RecExpr<SymbolLang>, ph_indices: Vec<(usize, String)>) -> RecExpr<SymbolLang> {
        let mut res = ex.as_ref().iter().cloned().collect_vec();
        for (i, new_ph) in ph_indices {
            res[i].op = Symbol::from(new_ph);
        }
        RecExpr::from(res)
    }

    fn collect_ph1s(&self, ex: &RecExpr<SymbolLang>) -> Vec<usize> {
        ex.as_ref().iter().enumerate()
            .filter(|s| s.1.op.as_str() == TheSy::get_ph(&self.datatype.as_exp(), 1).name)
            .map(|s| s.0).collect_vec()
    }

    pub fn rw_from_exp(precond: Option<&RecExpr<SymbolLang>>, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, ind_var: &Function) -> Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)> {
        let fixed_precond = precond.map(|p| Self::pattern_from_exp(p, &ind_var, &("?".to_owned() + &ind_var.name)));
        let fixed_ex1 = Self::pattern_from_exp(ex1, ind_var, &("?".to_owned() + &ind_var.name));
        let fixed_ex2 = Self::pattern_from_exp(ex2, ind_var, &("?".to_owned() + &ind_var.name));
        let precond_text = fixed_precond.as_ref().map_or("".to_owned(), |p| p.pretty_string() + " |> ");
        let text1 = precond_text.to_owned() + &*fixed_ex1.pretty(80) + " => " + &*fixed_ex2.pretty(80);
        let text2 = precond_text.to_owned() + &*fixed_ex2.pretty(80) + " => " + &*fixed_ex1.pretty(80);
        let mut new_rules: Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)> = vec![];
        // TODO: dont do it so half assed
        Prover::push_rw(fixed_precond.clone(), &fixed_ex1, &fixed_ex2, text1, &mut new_rules);
        Prover::push_rw(fixed_precond, &fixed_ex2, &fixed_ex1, text2, &mut new_rules);
        new_rules
    }

    pub fn prove_base(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> bool {
        self.prove_base_split_d(case_splitter, rules, None, ex1, ex2, Self::CASE_SPLIT_DEPTH)
    }

    pub fn prove_base_split_d(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], precond: Option<&RecExpr<SymbolLang>>, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, split_d: usize) -> bool {
        if self.not_containing_ind_var(ex1) && self.not_containing_ind_var(ex2) {
            return false;
        }
        // create graph containing both expressions
        let (orig_egraph, ind_id) = self.create_proof_graph(precond, &ex1, &ex2);
        self.datatype.constructors.iter().filter(|c| c.params.is_empty()).all(|c| {
            let mut egraph = orig_egraph.clone();
            let contr_id = egraph.add_expr(&c.as_exp());
            egraph.union(contr_id, ind_id);
            let mut runner: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).with_iter_limit(Self::RUN_DEPTH).run(&rules[..]);
            case_splitter.iter_mut().for_each(|c| c.case_split(&mut runner.egraph, split_d, &rules, Self::CASE_SPLIT_RUN));
            !runner.egraph.equivs(&ex1, &ex2).is_empty()
        })
    }

    pub fn generalize_prove(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], orig_ex1: &RecExpr<SymbolLang>, orig_ex2: &RecExpr<SymbolLang>)
                            -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        // TODO: generalize non induction vars
        let mut ex1 = orig_ex1.into_tree().to_clean_exp();
        let mut ex2 = orig_ex2.into_tree().to_clean_exp();

        let mut ex1_ph1_indices = self.collect_ph1s(&ex1);
        let mut ex2_ph1_indices = self.collect_ph1s(&ex2);
        if ex1_ph1_indices.len() <= 1 && ex2_ph1_indices.len() <= 1 {
            return None;
        }
        if ex1_ph1_indices.len() > ex2_ph1_indices.len() {
            std::mem::swap(&mut ex1_ph1_indices, &mut ex2_ph1_indices);
            std::mem::swap(&mut ex1, &mut ex2);
        }
        info!("generalizing {} = {}", ex1.pretty(500), ex2.pretty(500));
        // We want less options when checking all permutations
        let max_phs = max(ex2_ph1_indices.len(), ex1_ph1_indices.len());
        let mut res = None;
        for ph_count in (1..=max_phs).rev() {
            let updated_ex2 = Self::replace_at_indexes(
                &ex2,
                ex2_ph1_indices.iter().enumerate().map(|(ph_id, index)|
                    (*index, TheSy::get_ph(&self.datatype.as_exp(), (ph_id % ph_count) + 1).name)).collect_vec(),
            );
            let control = heap_recursive(&mut ex1_ph1_indices, |permutation| {
                let updated_ex1 = Self::replace_at_indexes(
                    &ex1,
                    permutation.iter().enumerate().map(|(ph_id, index)|
                        (*index, TheSy::get_ph(&self.datatype.as_exp(), (ph_id % ph_count) + 1).name)).collect_vec(),
                );
                let res = self.prove_all(case_splitter, rules, &updated_ex1, &updated_ex2);
                if res.is_some() {
                    Control::Break(res.unwrap())
                } else {
                    Control::Continue
                }
            });
            res = control.break_value();
            if res.is_some() {
                break;
            }
        }
        res
    }

    /// Returns Some if found rules otherwise None. Receives expressions without vars.
    pub fn prove_ind(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>)
                     -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        self.prove_ind_split_d(case_splitter, rules, None, ex1, ex2, Self::CASE_SPLIT_DEPTH)
    }

    /// Assume base case is correct and prove equality using induction.
   /// Induction hypothesis is given as a rewrite rule, using precompiled rewrite rules
   /// representing well founded order on the induction variable.
   /// Need to replace the induction variable with an expression representing a constructor and
   /// well founded order on the params of the constructor.
    pub fn prove_ind_split_d(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], precond: Option<&RecExpr<SymbolLang>>, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, split_d: usize)
                             -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        if self.not_containing_ind_var(ex1) && self.not_containing_ind_var(ex2) {
            return None;
        }
        // rewrites to encode proof
        let mut rule_set = Self::create_hypothesis(&self.ind_var, precond, &ex1, &ex2);
        let wfo_rws = &self.wfo_rules;
        rule_set.extend(rules.iter().cloned());
        rule_set.extend(wfo_rws.iter().cloned());
        // create graph containing both expressions
        let (orig_egraph, ind_id) = self.create_proof_graph(precond, &ex1, &ex2);
        let mut res = true;
        for c in self.datatype.constructors.iter().filter(|c| !c.params.is_empty()) {
            let mut egraph = orig_egraph.clone();
            let contr_exp = RecExpr::from_str(format!("({} {})", c.name, c.params.iter().enumerate()
                .map(|(i, t)| "param_".to_owned() + &*i.to_string())
                .intersperse(" ".parse().unwrap()).collect::<String>()).as_str()).unwrap();
            let contr_id = egraph.add_expr(&contr_exp);
            egraph.union(contr_id, ind_id);
            let mut runner: Runner<SymbolLang, ()> = Runner::new(()).with_egraph(egraph).with_iter_limit(Self::RUN_DEPTH).run(&rule_set[..]);
            case_splitter.iter_mut().for_each(|c| c.case_split(&mut runner.egraph, split_d, &rule_set, Self::CASE_SPLIT_RUN));
            res = res && !runner.egraph.equivs(&ex1, &ex2).is_empty()
        }
        if res {
            Some(Self::rw_from_exp(precond, ex1, ex2, &self.ind_var))
        } else {
            info!("Failed to prove: {} = {}", ex1.pretty(500), ex2.pretty(500));
            None
        }
    }

    pub fn prove_all(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>)
                     -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        self.prove_all_split_d(case_splitter, rules, None, ex1, ex2, Self::CASE_SPLIT_DEPTH)
    }

    pub fn prove_all_split_d(&self, case_splitter: &mut Option<&mut CaseSplit>, rules: &[Rewrite<SymbolLang, ()>], precond: Option<&RecExpr<SymbolLang>>, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>, split_d: usize)
                             -> Option<Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>> {
        if self.prove_base_split_d(case_splitter, rules, precond, ex1, ex2, split_d) {
            self.prove_ind_split_d(case_splitter, rules, precond, ex1, ex2, split_d)
        } else {
            None
        }
    }

    fn push_rw(precond: Option<Pattern<SymbolLang>>, fixed_ex1: &Pattern<SymbolLang>, fixed_ex2: &Pattern<SymbolLang>, text1: String, new_rules: &mut Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>) {
        if !fixed_ex1.ast.as_ref().last().unwrap().is_leaf() {
            let rw = if precond.is_some() {
                Rewrite::new(text1.clone(), MultiDiffSearcher::new(vec![precond.clone().unwrap(), fixed_ex1.clone()]), fixed_ex2.clone())
            } else {
                Rewrite::new(text1.clone(), fixed_ex1.clone(), fixed_ex2.clone())
            };
            if rw.is_ok() {
                new_rules.push((precond, fixed_ex1.clone(), fixed_ex2.clone(), rw.unwrap()));
            } else {
                debug!("Err creating rewrite, probably existential");
                debug!("{}", precond.map_or("".to_owned(), |p| (p.pretty_string() + " |> ")) + &*fixed_ex1.pretty(80) + " => " + &*fixed_ex2.pretty(80));
            }
        }
    }

    fn create_hypothesis(induction_ph: &Function, precond: Option<&RecExpr<SymbolLang>>, ex1: &RecExpr<SymbolLang>, ex2: &RecExpr<SymbolLang>) -> Vec<Rewrite<SymbolLang, ()>> {
        assert!(!induction_ph.name.starts_with("?"));
        // used somevar but wasnt recognised as var
        let ind_replacer = "?somevar".to_string();
        let clean_term1 = Self::pattern_from_exp(ex1, induction_ph, &ind_replacer);
        let clean_term2 = Self::pattern_from_exp(ex2, induction_ph, &ind_replacer);
        let pret = clean_term1.pretty(500);
        let pret2 = clean_term2.pretty(500);
        let mut searchers = vec![EitherSearcher::left(Pattern::from_str(&*format!("({} {} {})", Self::wfo_op(), ind_replacer, induction_ph.name)).unwrap())];
        precond.map(|p| searchers.push(EitherSearcher::right(MultiEqSearcher::new(vec![Pattern::from(p.as_ref()), Pattern::from_str("true").unwrap()]))));
        let precondition = MultiDiffSearcher::new(searchers);
        let precond_pret = precondition.pretty_string();
        let mut res = vec![];
        // Precondition on each direction of the hypothesis
        if pret.starts_with("(") {
            let searcher = MultiDiffSearcher::new(vec![EitherSearcher::left(clean_term1.clone()), EitherSearcher::right(precondition.clone())]);
            let rw = Rewrite::new("IH1", searcher, clean_term2.clone());
            if rw.is_ok() {
                res.push(rw.unwrap())
            } else {
                info!("Failed to add rw, probably existential");
                info!("{} |> {} => {}", precond_pret, pret, pret2);
            }
        }
        if pret2.starts_with("(") {
            let searcher = MultiDiffSearcher::new(vec![EitherSearcher::left(clean_term2.clone()), EitherSearcher::right(precondition.clone())]);
            let rw = Rewrite::new("IH2", searcher, clean_term1.clone());
            if rw.is_ok() {
                res.push(rw.unwrap())
            } else {
                info!("Failed to add rw, probably existential");
                info!("{} |> {} => {}", precond_pret, pret2, pret);
            }
        }
        res
    }

    pub fn pattern_from_exp(exp: &RecExpr<SymbolLang>, induction_ph: &Function, sub_ind: &String) -> Pattern<SymbolLang> {
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
        Pattern::from(res_exp.into_tree().to_clean_exp())
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

#[cfg(test)]
mod tests {
    use egg::{EGraph, Pattern, Runner, Searcher, SymbolLang};

    use crate::lang::{DataType, Function};
    use crate::thesy::prover::Prover;
    use crate::TheSyConfig;
    use crate::thesy::TheSy;

    fn create_nat_type() -> DataType {
        DataType::new("nat".to_string(), vec![
            Function::new("Z".to_string(), vec![], "nat".parse().unwrap()),
            Function::new("S".to_string(), vec!["nat".parse().unwrap()], "nat".parse().unwrap()),
        ])
    }

    #[test]
    fn wfo_trans_ok() {
        let mut egraph = EGraph::default();
        egraph.add_expr("(ltwf x y)".parse().as_ref().unwrap());
        egraph.add_expr("(ltwf y z)".parse().as_ref().unwrap());
        egraph = Runner::default().with_egraph(egraph).run(&vec![Prover::wfo_trans()][..]).egraph;
        let pat: Pattern<SymbolLang> = "(ltwf x z)".parse().unwrap();
        assert!(pat.search(&egraph).iter().all(|s| !s.substs.is_empty()));
        assert!(!pat.search(&egraph).is_empty());
    }

    #[test]
    fn wfo_nat_ok() {
        let mut egraph = EGraph::default();
        egraph.add_expr("(S y)".parse().as_ref().unwrap());
        egraph = Runner::default().with_egraph(egraph).run(&Prover::wfo_datatype(&create_nat_type())[..]).egraph;
        let pat: Pattern<SymbolLang> = "(ltwf y (S y))".parse().unwrap();
        assert!(pat.search(&egraph).iter().all(|s| !s.substs.is_empty()));
        assert!(!pat.search(&egraph).is_empty());
    }

    #[test]
    fn cant_prove_wrong() {
        let config = TheSyConfig::from_path("theories/list.th".parse().unwrap());
        let thesy = TheSy::from(&config);
        let p = thesy.datatypes.iter().next().unwrap().1;
        let res = p.prove_ind(&mut None, &config.definitions.rws, &"(append ts_ph_Lst_0 ts_ph_Lst_1)".parse().unwrap(), &"(append ts_ph_Lst_0 (append ts_ph_Lst_1 ts_ph_Lst_0))".parse().unwrap());
        assert!(res.is_none());
        //(append ?ts_ph_Lst_0 ?ts_ph_Lst_1) => (append ?ts_ph_Lst_0 (append ?ts_ph_Lst_0 ?ts_ph_Lst_0))
    }
}