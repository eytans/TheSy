use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use egg::{Pattern, RecExpr, Rewrite, Searcher, SymbolLang, Var, ENodeOrVar, Condition, ImmutableCondition, RcImmutableCondition};
use itertools::Itertools;
use thesy_parser::{grammar, ast};

use crate::lang::{DataType, Function};
use std::path::PathBuf;
use thesy_parser::ast::{Expression, Statement, Identifier, Annotation, Terminal};
use thesy_parser::ast::Definitions::Defs;
use std::str::FromStr;
use crate::eggstentions::searchers::multisearcher::{MultiEqSearcher, MultiDiffSearcher, EitherSearcher, FilteringSearcher, ToDyn, PointerSearcher};
use crate::thesy::TheSy;
use crate::eggstentions::appliers::DiffApplier;
use thesy_parser::ast::Terminal::{Id, Hole};
use thesy_parser::ast::Expression::{Op, Leaf};
use multimap::MultiMap;
use crate::eggstentions::expression_ops::{IntoTree, Tree};
use crate::eggstentions::conditions::{AndCondition, OrCondition};
use std::iter::FromIterator;

#[derive(Default, Clone)]
pub struct Definitions {
    /// All datatype definitions
    pub datatypes: Vec<DataType>,
    /// All function declereations as (name, type)
    pub functions: Vec<Function>,
    /// Rewrites defined by (assert forall)
    pub rws: Vec<Rewrite<SymbolLang, ()>>,
    /// Terms to prove, given as not forall, (vars - types, precondition, ex1, ex2)
    pub conjectures: Vec<(HashMap<RecExpr<SymbolLang>, RecExpr<SymbolLang>>, Option<RecExpr<SymbolLang>>, RecExpr<SymbolLang>, RecExpr<SymbolLang>)>,
    /// Logic of when to apply case split
    pub case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Pattern<SymbolLang>, Vec<Pattern<SymbolLang>>)>,
    /// patterns used to deduce case splits
    name_pats: Vec<(String, Expression)>,
    /// goals in ast format
    pub goals: Vec<(Option<Expression>, Expression, Expression)>,
}

impl Definitions {
    pub fn merge(&mut self, mut other: Self) {
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

    pub fn from_file(path: &PathBuf) -> Self {
        let text = std::fs::read_to_string(path).unwrap();
        let res = grammar::DefsParser::new().parse(&text);
        match res {
            Ok(x) => {
                match x {
                    Defs(stmts) => {
                        let res = Self::from(stmts);
                        info!("Read definitions:\n{}", res);
                        res
                    }
                }
            }
            Err(e) => {
                error!("{}", e);
                panic!("Please implement error handling")
            }
        }
    }

    fn exp_to_pattern(exp: &Expression) -> Pattern<SymbolLang> {
        Pattern::from_str(&*exp.to_sexp_string()).unwrap()
    }

    fn collect_non_pattern_conds(conds: Vec<ast::Condition>) -> Vec<RcImmutableCondition<SymbolLang, ()>> {
        conds.into_iter().map(|(matcher, negation)| {
            FilteringSearcher::create_non_pattern_filterer(
                FilteringSearcher::matcher_from_pattern(Self::exp_to_pattern(&matcher)),
                FilteringSearcher::matcher_from_pattern(Self::exp_to_pattern(&negation)))
        }).collect_vec()
    }

    fn create_searcher_applier(precond: Option<Expression>,
                               source: Expression,
                               target: Expression,
                               conds: Vec<thesy_parser::ast::Condition>)
                               -> (FilteringSearcher<SymbolLang, ()>, Pattern<SymbolLang>) {
        let precond_searcher = precond.as_ref().map(|e| {
            MultiEqSearcher::new(vec![Self::exp_to_pattern(e),
                                      Pattern::from_str("true").unwrap()])
        });
        let searcher = {
            let s = Self::exp_to_pattern(&source);
            if precond.is_some() {
                MultiDiffSearcher::new(vec![
                    EitherSearcher::left(s),
                    EitherSearcher::right(precond_searcher.unwrap()),
                ]).into_rc_dyn()
            } else {
                s.into_rc_dyn()
            }
        };
        let applier = Self::exp_to_pattern(&target);
        let conditions = Self::collect_non_pattern_conds(conds);
        let cond_searcher = FilteringSearcher::new(searcher,
                                                   RcImmutableCondition::new(AndCondition::new(conditions)));
        (cond_searcher, applier)
    }

    fn collect_splittable_params(&self, f: &Function, opt_pats: &Vec<Expression>)
                                 -> Vec<(usize, &DataType, RcImmutableCondition<SymbolLang, ()>)> {
        let param_types = f.params.iter().enumerate()
            // Get type of each param (if type exists)
            .filter_map(|p| Some(p.0).zip(
                self.datatypes.iter().find(|d| &d.as_exp() == p.1)))
            // Only keep params which have patterns for all constructors
            .filter(|(i, d)| d.constructors.iter()
                .all(|c| opt_pats.iter().any(|exp| {
                    // One of the patterns should equal be the constructor
                    &c.name == exp.children()[*i].root().ident()
                })))
            .collect_vec();


        param_types.into_iter().map(|(i, p_dt)| {
            // collect all patterns of other params for each constructor type
            let mut patterns_grouped: HashMap<String, Vec<&Expression>> = HashMap::default();
            for c in &p_dt.constructors {
                patterns_grouped.insert(c.name.clone(), opt_pats.into_iter()
                    .filter(|s| s.children()[i].root().ident() == &c.name)
                    .collect_vec(),
                );
            }

            // Can split by any param by itself by adding filterers on other params.
            // Instead of a very sophisticated runtime I am creating a complex pattern for asserting
            // the rewriting will continue in each split.
            // Should be And(<for each constructor c Or(for all pattern with c in place i where the subpattern in place i is replaced with a fresh hole)>)
            let cond = AndCondition::new(patterns_grouped.into_iter().map(|(name, pats)| {
                RcImmutableCondition::new(OrCondition::new(pats.into_iter().map(|exp| {
                    let holename = "splithole";
                    assert!(exp.holes().iter().find(|h| h.ident() == holename).is_none());
                    let mut new_children = exp.children().iter().cloned().collect_vec();
                    new_children[i] = Leaf(Hole(holename.to_string(), None));
                    let mut new_exp = Op(exp.root().clone(), new_children);
                    FilteringSearcher::create_exists_pattern_filterer(Self::exp_to_pattern(&new_exp))
                }).collect_vec()))
            }).collect_vec());
            (i, p_dt, RcImmutableCondition::new(cond))
        }).collect_vec()
    }

    // Not most efficient but still:
    // * Find an application of the function where all params are holes
    // * Add the condition
    // * For the splitted param create patterns with the param var as root (we don't split same var
    //    twice)


    fn create_splitters(datatype: &DataType, h: &thesy_parser::ast::Terminal) -> Vec<Expression> {
        datatype.constructors.iter().map(|c| {
            let const_name: Terminal = Id(c.name.clone(), None);
            if c.params.is_empty() {
                Leaf(const_name)
            } else {
                Op(const_name, (0..c.params.len())
                    .map(|i| Leaf(Id(format!("(param_{}_{} {})",
                                                     datatype.name, i, h.to_string()), None)))
                    .collect_vec(),
                )
            }
        }).collect_vec()
    }
}

impl From<Vec<Statement>> for Definitions {
    fn from(x: Vec<Statement>) -> Self {
        let mut res: Self = Default::default();
        let mut rw_definitions: MultiMap<String, Expression> = Default::default();
        for s in x {
            match s {
                Statement::RewriteDef(name, def) => {
                    let current = res.rws.len();
                    // TODO: remove clone
                    res.process_rw(name.clone(), def.clone());
                    if res.rws.len() > current {
                        let exps: Vec<Expression> = def.source_expressions().into_iter().cloned().collect_vec();
                        for exp in exps {
                            rw_definitions.insert(exp.root().ident().clone(),
                                                  exp);
                        }
                    }
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
                Statement::CaseSplit(searcher, expr, pats, conditions) => {
                    let searcher = Pattern::from_str(&*searcher.to_sexp_string()).unwrap().into_rc_dyn();
                    let conditions = Self::collect_non_pattern_conds(conditions);
                    let cond_searcher = FilteringSearcher::new(searcher,
                                                               RcImmutableCondition::new(AndCondition::new(conditions)));
                    res.case_splitters.push((
                        cond_searcher.into_rc_dyn(),
                        Self::exp_to_pattern(&expr),
                        pats.iter().map(|x|
                            Pattern::from_str(&*x.to_sexp_string()).unwrap()).collect_vec()))
                }
            }
        }


        fn create_hole_for_param(i: usize) -> Terminal {
            Hole(format!("?autovar_{}", i), None)
        }

        fn pattern_for_func_app(f: &Function) -> Pattern<SymbolLang> {
            Definitions::exp_to_pattern(
                &Op(Id(f.name.clone(), None), (0..f.params.len())
                    .into_iter().map(|i| Leaf(create_hole_for_param(i))).collect_vec())
            )
        }

        // Foreach function find if and when case split should be applied
        for f in &res.functions {
            let opt_pats =
                if rw_definitions.contains_key(&f.name) { rw_definitions.get_vec(&f.name).unwrap() } else { continue; };
            let splittable_params = Self::collect_splittable_params(&res, f, opt_pats);
            let func_pattern = pattern_for_func_app(f).into_rc_dyn();
            let mut temp = vec![];
            for (i, dt, cond) in splittable_params {
                let param_hole = create_hole_for_param(i);
                let const_cond = RcImmutableCondition::new(AndCondition::new(
                    dt.constructors.iter().map(|c| {
                        FilteringSearcher::create_non_pattern_filterer(
                            FilteringSearcher::matcher_from_var(Var::from_str(&param_hole.to_string()).unwrap()),
                            FilteringSearcher::matcher_from_pattern(pattern_for_func_app(c))
                        )
                    }).collect_vec()
                ));
                let final_condition = RcImmutableCondition::new(AndCondition::new(vec![const_cond, cond]));
                let splitters = Self::create_splitters(dt, &param_hole).iter()
                    .map(Self::exp_to_pattern).collect_vec();
                temp.push((
                    FilteringSearcher::new(func_pattern.clone(), final_condition).into_rc_dyn(),
                    Self::exp_to_pattern(&Leaf(param_hole.clone())),
                    splitters));
            }
            res.case_splitters.extend_from_slice(&temp);
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
            write!(f, "  {}", rw)?;
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
                    Self::create_searcher_applier(precond, source, target, conds);
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
        // let mut constr_rewrites = vec![];
        // for (c_name, c_params) in constructors {
        //     format!("match <Exp> with <Const> => <Exp> (| <Const> => <Exp>)* ");
        //     constructors_patterns.push(format!("({} {})",
        //                                        c_name,
        //                                        c_params.iter().map(|x|
        //                                            format!("?{}", x.0)).join(" "))
        //     );
        // }
        // let searcher = Pattern::from_str(format!("(match ?x {})", )).unwrap();
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
            // let source = Pattern::from_str(&*format!("({} {})", name, param_names.join(" "))).unwrap();
            let source = Expression::Op(Id(name.clone(), None), param_names.into_iter().map(|n| Expression::Leaf(Id(n, None))).collect_vec());
            // let target = Pattern::from_str(&*e.to_sexp_string()).unwrap();
            let target = e;
            let rw = self.make_rw(format!("{}_def", name.clone()), None, source.clone(), target.clone(), vec![]);
            self.rws.push(rw);
            let rw = self.make_rw(format!("{}_def_rev", name.clone()), None, target.clone(), source, vec![]);
            self.rws.push(rw);
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
               conds: Vec<thesy_parser::ast::Condition>) -> Rewrite<SymbolLang, ()> {
        let (cond_searcher, applier) =
            Self::create_searcher_applier(precond, source.clone(), target, conds);
        if let Op(op, params) = &source {
            if op.is_id() {
                self.name_pats.push((op.ident().clone(), source));
            }
        }
        Rewrite::new(name, cond_searcher, applier).unwrap()
    }
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
