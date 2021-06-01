use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use egg::{Pattern, RecExpr, Rewrite, Searcher, SymbolLang, Var, ENodeOrVar};
use itertools::Itertools;
use thesy_parser::{grammar, ast};

use crate::lang::{DataType, Function};
use std::path::PathBuf;
use thesy_parser::ast::{Expression, Statement, Identifier, Annotation};
use thesy_parser::ast::Definitions::Defs;
use std::str::FromStr;
use crate::eggstentions::searchers::multisearcher::{MultiEqSearcher, MultiDiffSearcher,
                                                    EitherSearcher, FilteringSearcher,
                                                    ToDyn, aggregate_conditions, PointerSearcher};
use crate::thesy::TheSy;
use crate::eggstentions::appliers::DiffApplier;
use thesy_parser::ast::Terminal::{Id, Hole};
use thesy_parser::ast::Expression::Op;
use multimap::MultiMap;
use crate::eggstentions::expression_ops::{IntoTree, Tree};

#[derive(Default, Clone)]
pub struct Definitions {
    /// All datatype definitions
    pub datatypes: Vec<DataType>,
    /// All function declereations as (name, type)
    pub functions: Vec<Function>,
    /// Rewrites defined by (assert forall)
    pub rws: Vec<Rewrite<SymbolLang, ()>>,
    /// Terms to prove, given as not forall, (vars - types, precondition, ex1, ex2)
    pub conjectures: Vec<(HashMap <RecExpr<SymbolLang>, RecExpr<SymbolLang>>, Option<RecExpr<SymbolLang>>, RecExpr<SymbolLang>, RecExpr<SymbolLang>)>,
    /// Logic of when to apply case split
    pub case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Var, Vec<Pattern<SymbolLang>>)>,
    /// patterns used to deduce case splits
    name_pats: Vec<(String, Expression)>,
    /// goals in ast format
    pub goals: Vec<(Option<Expression>, Expression, Expression)>
}

impl Definitions {
    pub fn merge(&mut self, mut other: Definitions) {
        self.functions.extend_from_slice(&std::mem::take(&mut other.functions).into_iter()
            .filter(|f| self.functions.iter()
                .all(|f1| f1.name != f.name)).collect_vec());
        self.datatypes.extend_from_slice(&std::mem::take(&mut other.datatypes).into_iter()
            .filter(|d| self.datatypes.iter()
                .all(|d1| d1.name != d.name)).collect_vec());
        self.conjectures.extend_from_slice(
            &std::mem::take(&mut other.conjectures).into_iter()
                    .filter(|c| !self.conjectures.contains(c)).collect_vec());
        self.rws.extend_from_slice(&std::mem::take(&mut other.rws).into_iter()
            .filter(|rw| {
                self.rws.iter()
                    .all(|rw1| {
                        rw1.name() != rw.name()
                    })
            }).collect_vec());
        self.case_splitters.extend(std::mem::take(&mut other.case_splitters));
    }

    pub fn from_file(path: &PathBuf) -> Definitions {
        let text = std::fs::read_to_string(path).unwrap();
        let res = grammar::DefsParser::new().parse(&text);
        match res {
            Ok(x) => {
                match x {
                    Defs(stmts) => {
                        let res = Definitions::from(stmts);
                        info!("Read definitions:\n{}", res);
                        res
                    }
                }
            },
            Err(e) => {
                error!("{}", e);
                panic!("Please implement error handleing")
            }
        }
    }

    fn exp_to_pattern(exp: &Expression) -> Pattern<SymbolLang> {
        Pattern::from_str(&*exp.to_sexp_string()).unwrap()
    }

    fn create_searcher_applier(precond: Option<Expression>,
                               source: Expression,
                               target: Expression,
                               conds: Vec<(thesy_parser::ast::Terminal, Expression)>)
        -> (FilteringSearcher<SymbolLang, ()>, Pattern<SymbolLang>) {
        let precond_searcher = precond.as_ref().map(|e| {
            MultiEqSearcher::new(vec![Definitions::exp_to_pattern(e),
                                      Pattern::from_str("true").unwrap()])
        });
        let searcher = {
            let s = Definitions::exp_to_pattern(&source);
            if precond.is_some() {
                MultiDiffSearcher::new(vec![
                    EitherSearcher::left(s),
                    EitherSearcher::right(precond_searcher.unwrap())
                ]).into_rc_dyn()
            } else {
                s.into_rc_dyn()
            }
        };
        let applier = Definitions::exp_to_pattern(&target);
        let conditions = conds.into_iter().map(|(t, e)| {
            FilteringSearcher::create_non_pattern_filterer(
                Definitions::exp_to_pattern(&e).into_rc_dyn(),
                Var::from_str(&*t.to_string()).unwrap())
        }).collect_vec();
        let cond_searcher = FilteringSearcher::new(searcher,
                                                   aggregate_conditions(conditions));
        (cond_searcher, applier)
    }
}

impl From<Vec<Statement>> for Definitions {
    fn from(x: Vec<Statement>) -> Self {
        let mut res: Definitions = Default::default();
        for s in x {
            match s {
                Statement::RewriteDef(name, def) => {
                    res.process_rw(name, def)
                }
                Statement::Function(
                    name, params, ret, body) => {
                    res.process_fun(name, params, ret, body)
                }
                Statement::Datatype(name, type_params, constructors) => {
                    res.process_datatype(name, constructors);
                }
                Statement::Goal(precond, exp1, exp2) => {
                    res.process_goals(precond.as_ref(), &exp1, &exp2);
                    res.goals.push((precond, exp1, exp2));
                }
                Statement::CaseSplit(searcher, var, pats) => {
                    res.case_splitters.push((
                        Pattern::from_str(&*searcher.to_sexp_string()).unwrap().into_rc_dyn(),
                        Var::from_str(&*var.to_string()).unwrap(),
                        pats.iter().map(|x|
                            Pattern::from_str(&*x.to_sexp_string()).unwrap()).collect_vec()))
                }
            }
        }

        res
    }
}


impl std::fmt::Display for Definitions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "datatypes:")?;
        for d in &self.datatypes {
            write!(f, "  {}", d)?;
        }
        writeln!(f, "functions:")?;
        for fun in &self.functions {
            write!(f, "  {}", fun)?;
        }
        writeln!(f, "rewrites:")?;
        for rw in &self.rws {
            write!(f, "  ")?;
            rw.fmt(f)?;
            writeln!(f);
        }
        for c in &self.conjectures {
            write!(f, "  ")?;
            writeln!(f, "{} = {}", c.2, c.3)?;
        }
        write!(f, "case splitters len: {}", self.case_splitters.len())
    }
}

/// Helper functions for translating AST into semantic definitions
impl Definitions {
    fn process_rw(&mut self, name: String, def: ast::Rewrite) {
        match def {
            ast::Rewrite::DRewrite(
                precond, source, target, conds
            ) => {
                let rw = self.make_rw(name, precond, source, target, conds);
                self.rws.push(rw);
            }
            ast::Rewrite::BRewrite(
                precond, source, target, conds
            ) => {
                let rw = self.make_rw(name.clone(),
                                      precond.clone(),
                                      target.clone(),
                                      source.clone(),
                                      conds.clone());
                self.rws.push(rw);
                let rw = self.make_rw(name + "_rev", precond, source, target, conds);
                self.rws.push(rw);
            }
            ast::Rewrite::AddSearcher(
                precond, source, target, conds
            ) => {
                let (cond_searcher, applier) =
                    Definitions::create_searcher_applier(precond, source, target, conds);
                let diff_applier = DiffApplier::new(applier);
                self.rws.push(Rewrite::new(name, cond_searcher, diff_applier).unwrap());
            }
        }
    }

    fn process_datatype(&mut self, name: String, constructors: Vec<(String, Vec<(String, ast::Annotation)>)>) {
        let consts_funs = constructors.iter().map(|(name, params)| {
            let mut constr_params = params.iter()
                .map(|(_, anno)| RecExpr::from_str(
                    &*anno.get_type().unwrap().to_sexp_string())
                    .unwrap()).collect_vec();
            let ret = constr_params.pop().unwrap();
            Function::new(name.to_string(), constr_params, ret)
        }).collect_vec();
        self.datatypes.push(DataType::new(name, consts_funs));
    }

    fn process_fun(&mut self, name: String, params: Vec<(String, Annotation)>, ret: Annotation, body: Option<Expression>) {
        let param_types = params.iter()
            .map(|(i, a)|
                RecExpr::from_str(&*a.get_type().unwrap().to_sexp_string()).unwrap()
            ).collect_vec();
        let ret_type = RecExpr::from_str(
            &*ret.get_type().unwrap().to_sexp_string()
        ).unwrap();
        self.functions.push(Function::new(name.clone(), param_types, ret_type));
        body.iter().for_each(|e| {
            let param_names = params.iter()
                .map(|(i, a)| "?".to_owned() + i).collect_vec();
            self.rws.extend(rewrite!(format!("{}_def", name);
                            {Pattern::from_str(&*format!("({} {})", name, param_names.join(" "))).unwrap()}
                            <=> {Pattern::from_str(&*e.to_sexp_string()).unwrap()}));
        })
    }

    fn process_goals(&mut self, precond: Option<&Expression>, exp1: &Expression, exp2: &Expression) {
        let mut type_map = HashMap::new();
        let mut all_terminals = precond.iter()
            .flat_map(|e| e.terminals().iter().cloned().cloned().collect_vec())
            .collect_vec();
        all_terminals.extend(exp1.terminals().into_iter().cloned());
        all_terminals.extend(exp2.terminals().into_iter().cloned());
        for t in all_terminals {
            // No holes in goals
            if let Id(name, anno) = t {
                if let Some(ptr) = anno {
                    if let Some(typ) = ptr.get_type() {
                        type_map.insert(
                            RecExpr::from_str(&*name).unwrap(),
                            RecExpr::from_str(&*typ.to_sexp_string()).unwrap());
                    }
                }
            }
        }
        self.conjectures.push((type_map,
                    precond.map(|t|
                        RecExpr::from_str(&*t.to_sexp_string()).unwrap()),
                    RecExpr::from_str(&*exp1.to_sexp_string()).unwrap(),
                    RecExpr::from_str(&*exp2.to_sexp_string()).unwrap()));
    }

    fn make_rw(&mut self,
               name: String,
               precond: Option<Expression>,
               source: Expression,
               target: Expression,
               conds: Vec<(thesy_parser::ast::Terminal, Expression)>) -> Rewrite<SymbolLang, ()> {
        let (cond_searcher, applier) =
            Definitions::create_searcher_applier(precond, source.clone(), target, conds);
        if let Op(op, params) = &source {
            if op.is_id() {
                self.name_pats.push((op.ident().clone(), source));
            }
        }
        Rewrite::new(name, cond_searcher, applier).unwrap()
    }

    // fn deduce_case_splitters(&mut self) {
    //     let mut function_patterns: MultiMap<Function, Expression> = MultiMap::new();
    //
    //     for (name, pat) in &self.name_pats {
    //         let opt = self.functions.iter().find(|f| f.name == name);
    //         if opt.is_some() {
    //             function_patterns.insert(opt.unwrap().clone(), pat.clone());
    //         }
    //     }
    //
    //     fn get_splitters(datatype: &DataType, root_var: &ENodeOrVar<SymbolLang>) -> Vec<String> {
    //         datatype.constructors.iter().map(|c|
    //             if c.params.is_empty() {
    //                 c.name.clone()
    //             } else {
    //                 format!("({} {})", c.name, (0..c.params.len()).map(|i| format!("(param_{}_{} {})", datatype.name, i, root_var.display_op())).join(" "))
    //             }
    //         ).collect_vec()
    //     }
    //
    //     // Foreach function find if and when case split should be applied
    //     for f in &self.functions {
    //         if !function_patterns.contains_key(f) { continue; }
    //         let mut case_splitters = vec![];
    //         let pats = function_patterns.get_vec(f).unwrap();
    //
    //         let relevant_params = f.params.iter()
    //             .enumerate()
    //             .filter_map(|(i, t)| {
    //                 // For each param check whether it covers all of the datatype's constructors
    //                 // This means splitting makes sense as all cases can be expanded
    //                 let param_datatype = self.datatypes.iter().find(|d|
    //                     d.name == t.into_tree().root().op.to_string());
    //                 param_datatype.filter(|d| d.constructors.iter().all(|c|
    //                     pats.iter().any(|p|
    //                         p.children()[*i].root().ident() == c.name))
    //                 ).map(|d| (i, t, d));
    //                 // TODO: also filter by whether the other params are always the same or var and one pattern.
    //                 // TODO: if there is a pattern use it for screening
    //         });
    //
    //         let mut x = 0;
    //         let mut fresh_v = || {
    //             x = x + 1;
    //             Var::from_str(&*("?autovar".to_string() + &*x.to_string())).unwrap()
    //         };
    //
    //         let mut fresh_vars = |exp: RecExpr<ENodeOrVar<SymbolLang>>, vars: &mut HashMap<Var, Var>| {
    //             RecExpr::from(exp.as_ref().iter().cloned().map(|e| match e {
    //                 ENodeOrVar::ENode(n) => { ENodeOrVar::ENode(n) }
    //                 ENodeOrVar::Var(v) => {
    //                     if !vars.contains_key(&v) {
    //                         vars.insert(v, fresh_v());
    //                     }
    //                     ENodeOrVar::Var(vars[&v])
    //                 }
    //             }).collect_vec())
    //         };
    //
    //         // Match case split only when split will be possible by other params (not splitted ones)
    //         let param_pats = relevant_params.filter_map(|(i, t, d)| {
    //             let mut par_pats = (0..f.params.len()).map(|_| vec![]).collect_vec();
    //             for p in pats.iter().filter(|p|
    //                 // Take only patterns where the i param is being matched
    //                 match p.children()[i].root() {
    //                     Id(s, _) => { d.constructors.iter().any(|c| c.name == s.op.to_string()) }
    //                     Hole(_, _) => { false }
    //                 }) {
    //                 let mut vars = HashMap::new();
    //                 for j in 0..f.params.len() {
    //                     if i == j { continue; }
    //                     if let Id(par_pat, a) = p.children()[j].root() {
    //                         // replace vars
    //                         let replaced = fresh_vars(p.children()[j].clone(), &mut vars);
    //                         par_pats[j].push(replaced);
    //                     }
    //                 }
    //             }
    //             Some((i, d, par_pats)).filter(|(_, _, ps)| ps.iter().any(|v| !v.is_empty()))
    //         }).collect_vec();
    //
    //         param_pats.into_iter().flat_map(|(index, datatype, param_pat)| {
    //             let patterns_and_vars = param_pat.into_iter()
    //                 .map(|v|
    //                     if v.is_empty() {
    //                         let mut exp = RecExpr::default();
    //                         exp.add(ENodeOrVar::Var(fresh_v()));
    //                         vec![exp]
    //                     } else {
    //                         v
    //                     }).collect_vec();
    //             // let mut res: Vec<Rewrite<SymbolLang, ()>> = vec![];
    //             let mut res: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Var, Vec<Pattern<SymbolLang>>)> = vec![];
    //             for combs in combinations(patterns_and_vars.iter().cloned().map(|x| x.into_iter())) {
    //                 let mut nodes = vec![];
    //                 let children = combs.into_iter().map(|exp| {
    //                     let cur_len = nodes.len();
    //                     nodes.extend(exp.as_ref().iter().cloned().map(|s|
    //                         match s {
    //                             ENodeOrVar::ENode(n) => {
    //                                 ENodeOrVar::ENode(n.map_children(|child| Id::from(usize::from(child) + cur_len)))
    //                             }
    //                             ENodeOrVar::Var(v) => { ENodeOrVar::Var(v) }
    //                         }));
    //                     Id::from(nodes.len() - 1)
    //                 }).collect_vec();
    //                 nodes.push(ENodeOrVar::ENode(SymbolLang::new(&f.name, children)));
    //                 let searcher = Pattern::from(RecExpr::from(nodes));
    //                 println!("Searcher: {}", searcher.pretty_string());
    //                 let root_var: &ENodeOrVar<SymbolLang> = searcher.ast.into_tree().children()[index].root();
    //                 let root_v_opt = if let &ENodeOrVar::Var(v) = root_var {
    //                     Some(v)
    //                 } else {
    //                     None
    //                 };
    //                 let mut cond_texts = vec![];
    //                 let searcher_conditions = datatype.constructors.iter().map(|c| c.apply_params(
    //                     (0..c.params.len()).map(|i| RecExpr::from_str(&*("?param_".to_owned() + &*i.to_string())).unwrap()).collect_vec()
    //                 )).map(|exp| {
    //                     cond_texts.push(format!("Cond(var: {}, pat: {})", root_v_opt.as_ref().unwrap().to_string(), exp.pretty(1000)));
    //                     FilteringSearcher::create_non_pattern_filterer(Pattern::from_str(&*exp.pretty(1000)).unwrap().into_rc_dyn(), root_v_opt.unwrap())
    //                 }).collect_vec();
    //                 let dyn_searcher: Rc<dyn Searcher<SymbolLang, ()>> = Rc::new(searcher.clone());
    //                 let conditonal_searcher = searcher_conditions.into_iter().fold(dyn_searcher, |pattern, y| {
    //                     Rc::new(FilteringSearcher::new(pattern, y))
    //                 });
    //
    //                 // For now pass the searcher, a condition and expressions for root and
    //                 // splits. Should be (Searcher, root_var, children_expr, conditions)
    //                 // res.push(Rewrite::new(rule_name, searcher, DiffApplier::new(ConditionalApplier { applier, condition: cond })).unwrap());
    //                 res.push((conditonal_searcher.clone(),
    //                           root_v_opt.unwrap(),
    //                           get_splitters(datatype, root_var).iter().map(|x| Pattern::from_str(x).unwrap()).collect_vec()));
    //             }
    //             res
    //         }).collect_vec();
    //         res.case_splitters.extend(case_splitters);
    //     }
    // }
}

#[cfg(test)]
mod test {
    use crate::thesy::semantics::Definitions;
    use std::path::PathBuf;

    #[test]
    fn parse_libs() {
        let defs = Definitions::from_file(&PathBuf::from("theories/list.th"));
        assert!(!defs.functions.is_empty());
        assert!(defs.conjectures.is_empty());
        assert!(!defs.datatypes.is_empty());
        assert!(!defs.rws.is_empty());
        assert!(defs.case_splitters.is_empty());
    }
}
