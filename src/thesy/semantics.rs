use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::rc::Rc;

use egg::{Pattern, RecExpr, Rewrite, Searcher, SymbolLang, Var, ENodeOrVar, Condition, ImmutableCondition, Language, RcImmutableCondition, ToCondRc};
use itertools::Itertools;
use thesy_parser::{grammar, ast};

use crate::lang::{DataType, Function, ThExpr, ThRewrite};
use std::path::PathBuf;
use thesy_parser::ast::{Expression, Statement, Identifier, Annotation, Terminal};
use thesy_parser::ast::Definitions::Defs;
use std::str::FromStr;
use egg::searchers::{MultiDiffSearcher, EitherSearcher, FilteringSearcher, ToDyn, PointerSearcher};
use crate::thesy::TheSy;
use egg::appliers::DiffApplier;
use thesy_parser::ast::Terminal::{Id, Hole};
use thesy_parser::ast::Expression::{Op, Leaf};
use multimap::MultiMap;
use egg::expression_ops::{IntoTree, RecExpSlice, Tree};
use egg::conditions::{AndCondition, OrCondition};
use std::iter::FromIterator;
use std::sync::atomic::{AtomicUsize, Ordering};
use indexmap::{IndexMap, IndexSet};
use egg::searchers::{PatternMatcher, ToRc, VarMatcher};
use crate::utils::SubPattern;

lazy_static!(
    static ref split_hole: Terminal = Hole(String::from("splithole"), None);
);

pub trait ToExpression<'a> {
    fn to_expression(&'a self) -> Expression;
}

impl<'a> ToExpression<'a> for RecExpSlice<'a, ENodeOrVar<SymbolLang>> {
    fn to_expression(&'a self) -> Expression {
        let op = self.root().display_op().to_string();
        let term = if self.is_root_hole() { Hole(op.replace("?", ""), None) } else { Id(op, None) };
        if !self.is_leaf() {
            let mut children = vec![];
            for c in self.children() {
                children.push(c.to_expression());
            }
            Op(term, children)
        } else {
            Leaf(term)
        }
    }
}

impl<'a> ToExpression<'a> for Pattern<SymbolLang> {
    fn to_expression(&'a self) -> Expression {
        self.ast.into_tree().to_expression()
    }
}

#[derive(Default, Clone)]
pub struct Definitions {
    /// All datatype definitions
    pub datatypes: Vec<DataType>,
    /// All function declereations as (name, type)
    pub functions: Vec<Function>,
    /// Rewrites defined by (assert forall)
    pub rws: Vec<ThRewrite>,
    /// Terms to prove, given as not forall, (vars - types, holes, precondition, ex1, ex2)
    pub conjectures: Vec<(IndexMap<ThExpr, ThExpr>, IndexSet<ThExpr>, Option<ThExpr>, ThExpr, ThExpr)>,
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
        self.goals.extend(std::mem::take(&mut other.goals));
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

    pub fn exp_to_pattern(exp: &Expression) -> Pattern<SymbolLang> {
        let exp_s = exp.to_sexp_string();
        Pattern::from_str(&*exp_s).unwrap()
    }

    fn collect_non_pattern_conds(conds: Vec<ast::Condition>) -> Vec<RcImmutableCondition<SymbolLang, ()>> {
        conds.into_iter().map(|(matcher, negation)| {
            let p1= Self::exp_to_pattern(&matcher);
            let p2 = Self::exp_to_pattern(&negation);
            FilteringSearcher::create_non_pattern_filterer(
                PatternMatcher::new(p1).into_rc(),
                PatternMatcher::new(p2).into_rc(),
            )
        }).collect_vec()
    }

    fn create_searcher_applier(precond: Option<Expression>,
                               source: Expression,
                               target: Expression,
                               conds: Vec<thesy_parser::ast::Condition>)
                               -> (Rc<dyn Searcher<SymbolLang, ()>>, Pattern<SymbolLang>) {
        let precond_searcher = precond.as_ref().map(|e| {
            FilteringSearcher::searcher_is_true(Self::exp_to_pattern(e))
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
        debug_assert!(conditions.iter().all(|c| c.vars().iter().all(|v| searcher.vars().contains(v))));
        let cond_searcher =
            if conditions.is_empty() { searcher }
            else { FilteringSearcher::new(searcher,
                       AndCondition::new(conditions).into_rc()).into_rc_dyn()
            };
        (cond_searcher, applier)
    }

    fn collect_splittable_params<'a>(&self, f: &Function, opt_pats: &'a Vec<Expression>)
                                 -> Vec<(usize, &DataType, IndexMap<String, Vec<&'a Expression>>)> {
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
        if param_types.len() < 2 {
            return vec![];
        }

        param_types.into_iter().map(|(i, p_dt)| {
            // collect all patterns of other params for each constructor type
            let mut patterns_grouped: IndexMap<String, Vec<&Expression>> = IndexMap::default();
            for c in &p_dt.constructors {
                patterns_grouped.insert(c.name.clone(), opt_pats.into_iter()
                    .filter(|s| s.children()[i].root().ident() == &c.name)
                    .collect_vec(),
                );
            }

            // let cond = Self::condition_from_grouped_patterns(i, patterns_grouped);
            (i, p_dt, patterns_grouped)
        }).collect_vec()
    }

    fn condition_from_grouped_patterns(orig:&Expression, i: usize, patterns_grouped: IndexMap<String, Vec<&Expression>>) -> AndCondition<SymbolLang, ()> {
        // Can split by any param by itself by adding filterers on other params.
        // Instead of a very sophisticated runtime I am creating a complex pattern for asserting
        // the rewriting will continue in each split.
        // Should be And(<for each constructor c Or(for all pattern with c in place i where the subpattern in place i is replaced with a fresh hole)>)

        // TODO: Careful! currently have a hacky way to make pattern expression holes match the
        //       searcher for case split. In the future make this generic.
        let cond = AndCondition::new(patterns_grouped.into_iter().map(|(name, pats)| {
            OrCondition::new(pats.into_iter().map(|exp| {
                assert!(exp.holes().iter().find(|h| h.ident() == split_hole.ident()).is_none());
                let mut new_children = exp.children().iter().cloned().collect_vec();
                new_children[i] = Leaf(split_hole.clone());
                let mut new_exp = Op(exp.root().clone(), new_children);
                // TODO: new_exp should change param names to fit the seacher being created
                let subpattern = SubPattern::new(orig.clone(), Self::exp_to_pattern(&new_exp));
                subpattern.into_rc()
            }).collect_vec()).into_rc()
        }).collect_vec());
        cond
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
                    let conditions = conditions.into_iter().map(|(m, n)| {
                        let mp = Definitions::exp_to_pattern(&m);
                        let np = Definitions::exp_to_pattern(&n);
                        FilteringSearcher::create_non_pattern_filterer(
                            PatternMatcher::new(mp).into_rc(),
                            PatternMatcher::new(np).into_rc())
                    }).collect_vec();
                    let cond_searcher = FilteringSearcher::new(searcher,
                                                               AndCondition::new(conditions).into_rc());
                    res.case_splitters.push((
                        cond_searcher.into_rc_dyn(),
                        Self::exp_to_pattern(&expr),
                        pats.iter().map(|x|
                            Pattern::from_str(&*x.to_sexp_string()).unwrap()).collect_vec()))
                }
            }
        }


        fn create_hole_for_param(i: usize) -> Terminal {
            Hole(format!("autovar_{}", i), None)
        }

        fn pattern_for_func_app(f: &Function, hole_i: usize) -> Pattern<SymbolLang> {
            Definitions::exp_to_pattern(
                &Op(Id(f.name.clone(), None), (0..f.params.len()).into_iter().map(|i|
                    if hole_i == i {
                        Leaf(split_hole.clone())
                    } else {
                        Leaf(create_hole_for_param(i))
                    }
                ).collect_vec())
            )
        }

        // Foreach function find if and when case split should be applied
        for f in &res.functions {
            let opt_pats = if rw_definitions.contains_key(&f.name) {
                    rw_definitions.get_vec(&f.name).unwrap()
                } else {
                    continue;
                };
            let splittable_params = Self::collect_splittable_params(&res, f, opt_pats);
            let mut temp = vec![];
            for (i, dt, grouped_patterns) in splittable_params {
                let func_pattern = pattern_for_func_app(f, i);
                let mut fixed_pattern_groups = IndexMap::new();
                for (c, patterns) in &grouped_patterns {
                    let mut fixed_patterns = vec![];
                    for p in patterns {
                        let mut fixed_pattern = p.clone();
                        let mut subs = vec![];
                        for (i, c) in pattern_for_func_app(f, i).ast.into_tree().children().into_iter().enumerate() {
                            // We know this is a hole because we created it.
                            let hole = c.root().display_op().to_string();
                            // If this is a hole we want them to have the same name in the whole exp
                            let exp_c = fixed_pattern.children()[i].root().clone();
                            if exp_c.is_hole() && exp_c.to_string() != hole {
                                subs.push((exp_c.to_string(), hole.to_string()));
                            }
                        }
                        let new_pat = fixed_pattern.map(&mut |t: &Terminal| subs.iter()
                            .find(|&(a, b)| a == &t.to_string())
                            .map(|(a, b)| Hole(b.replace("?", ""), t.anno().clone()))
                            .unwrap_or(t.clone()));
                        fixed_patterns.push(new_pat);
                    }
                    fixed_pattern_groups.insert(c, fixed_patterns);
                }
                let referenced_fixed_groups = fixed_pattern_groups.iter()
                    .map(|(c, p)| (c.clone().clone(), p.iter().collect_vec()))
                    .collect();
                let cond = Self::condition_from_grouped_patterns(&func_pattern.to_expression(), i, referenced_fixed_groups).into_rc();
                let param_hole = split_hole.clone();
                let const_cond = AndCondition::new(
                    dt.constructors.iter().map(|c| {
                        let v = Var::from_str(&param_hole.to_string()).unwrap();
                        // HACK: We use a very large number here to make sure that the pattern
                        // matcher will not use ?splithole
                        let p = Definitions::exp_to_pattern(
                            &Op(Id(c.name.clone(), None),
                                (0..c.params.len()).into_iter()
                                    .map(|i| Leaf(create_unique_hole()))
                                    .collect_vec()));
                        FilteringSearcher::create_non_pattern_filterer(
                            VarMatcher::new(v).into_rc(),
                            PatternMatcher::new(p).into_rc())
                    }).collect_vec()
                ).into_rc();
                trace!("Working on condition for splitting function: {}", f.name);
                trace!("condition: {}", cond.describe());
                trace!("const cond: {}", const_cond.describe());

                let final_condition = AndCondition::new(vec![const_cond, cond]).into_rc();
                let splitters = Self::create_splitters(dt, &param_hole).iter()
                    .map(Self::exp_to_pattern).collect_vec();
                temp.push((
                    FilteringSearcher::new(func_pattern.into_rc_dyn(), final_condition).into_rc_dyn(),
                    Self::exp_to_pattern(&Leaf(param_hole.clone())),
                    splitters));
                warn!("adding Searcher: {}; Param hole: {}; Splitters: {}", &temp.last().unwrap().0.to_string(), temp.last().unwrap().1.to_string(), temp.last().unwrap().2.iter().join(", "));
            }
            res.case_splitters.extend_from_slice(&temp);
        }
        res
    }
}

static mut HOLE_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn create_unique_hole() -> Terminal {
    let i = unsafe { HOLE_COUNTER.fetch_add(1, Ordering::SeqCst) };
    Hole(format!("unique_autovar_{}", i), None)
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
            writeln!(f, "Forall {}. {} = {}", c.2.iter().join(", "), c.3, c.4)?;
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
                self.rws.push(Rewrite::new(name, PointerSearcher::new(cond_searcher), diff_applier).unwrap());
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
        let mut type_map = IndexMap::new();
        let mut holes = IndexSet::new();
        let mut all_terminals = precond.iter()
            .flat_map(|e| e.terminals().iter().cloned().cloned().collect_vec())
            .collect_vec();
        all_terminals.extend(exp1.terminals().into_iter().cloned());
        all_terminals.extend(exp2.terminals().into_iter().cloned());

        for t in all_terminals {
            let name = t.ident().clone();
            let anno = t.anno().clone();

            if t.is_hole() {
                holes.insert(RecExpr::from_str(&*name).unwrap());
                debug_assert!(!t.ident().starts_with("?"));
            }

            if let Some(ptr) = anno {
                if let Some(typ) = ptr.get_type() {
                    type_map.insert(
                        RecExpr::from_str(&*name).unwrap(),
                        RecExpr::from_str(&*typ.to_sexp_string()).unwrap());
                }
            }
        }

        fn hole_to_id(t: &Terminal) -> Terminal {
            match t {
                Hole(id, a) => Id(id.clone(), a.clone()),
                _ => t.clone()
            }
        }

        self.conjectures.push((type_map, holes,
                               precond.map(|t|
                                   RecExpr::from_str(&*t.map(&mut hole_to_id).to_sexp_string()).unwrap()),
                               RecExpr::from_str(&*exp1.map(&mut hole_to_id).to_sexp_string()).unwrap(),
                               RecExpr::from_str(&*exp2.map(&mut hole_to_id).to_sexp_string()).unwrap()));
    }

    fn make_rw(&mut self,
               name: String,
               precond: Option<Expression>,
               source: Expression,
               target: Expression,
               conds: Vec<thesy_parser::ast::Condition>) -> ThRewrite {
        let (cond_searcher, applier) =
            Self::create_searcher_applier(precond, source.clone(), target, conds);
        if let Op(op, params) = &source {
            if op.is_id() {
                self.name_pats.push((op.ident().clone(), source));
            }
        }
        Rewrite::new(name, PointerSearcher::new(cond_searcher), applier).unwrap()
    }
}

#[cfg(test)]
mod test {
    use crate::thesy::semantics::Definitions;
    use std::path::PathBuf;
    use egg::{EGraph, SymbolLang};
    use crate::tests::init_logging;
    use crate::thesy::case_split;
    use crate::thesy::case_split::CaseSplit;
    use crate::utils::filterTypings;

    #[test]
    fn parse_libs() {
        let defs = Definitions::from_file(&PathBuf::from("theories/list.th"));
        assert!(!defs.functions.is_empty());
        assert!(defs.conjectures.is_empty());
        assert!(!defs.datatypes.is_empty());
        assert!(!defs.rws.is_empty());
        assert!(defs.case_splitters.is_empty());
    }

    #[test]
    fn filter_constructors_from_case_split() {
        // load theories/goal1
        init_logging();

        let mut defs = Definitions::from_file(&PathBuf::from("theories/goal1.smt2.th"));
        // Create thesy and case splitter
        defs.case_splitters.remove(0);
        defs.case_splitters.remove(0);
        defs.case_splitters.remove(1);
        let mut splitter = CaseSplit::from_applier_patterns(defs.case_splitters);

        // let mut egraph: EGraph<SymbolLang, ()> = EGraph::new(());
        // let take_zero_exp = "(take zero (cons x (cons y nil)))".parse().unwrap();
        // let take_succ_i = egraph.add_expr(&take_zero_exp);
        // egraph.rebuild();
        // let found = splitter.find_splitters(&mut egraph);
        // assert_eq!(found.len(), 0);

        // let take_succ_nil_exp = "(take (succ i) nil)".parse().unwrap();
        // let take_succ_i = egraph.add_expr(&take_succ_nil_exp);
        // egraph.rebuild();
        // let found = splitter.find_splitters(&mut egraph);
        // assert_eq!(found.len(), 0);

        let mut egraph: EGraph<SymbolLang, ()> = EGraph::new(());
        let take_succ_i_exp = "(take (succ i) (cons x (cons y nil)))".parse().unwrap();
        let take_succ_i = egraph.add_expr(&take_succ_i_exp);
        egraph.rebuild();
        egraph.filtered_dot(|eg, id| filterTypings(eg, id))
            .to_dot("take_succ_i.dot".to_string()).unwrap();
        let found = splitter.find_splitters(&mut egraph);
        assert_eq!(found.len(), 0);
    }

    #[test]
    #[cfg(feature = "split_colored")]
    fn filter_constructors_from_colored_case_split() {
        // load theories/goal1
        init_logging();

        let mut defs = Definitions::from_file(&PathBuf::from("theories/goal1.smt2.th"));
        // Create thesy and case splitter
        defs.case_splitters.remove(0);
        defs.case_splitters.remove(0);
        defs.case_splitters.remove(1);
        let mut splitter = CaseSplit::from_applier_patterns(defs.case_splitters);

        let mut egraph: EGraph<SymbolLang, ()> = EGraph::new(());
        let take_succ_i_exp = "(take i (cons x (cons y nil)))".parse().unwrap();
        let take_succ_i = egraph.add_expr(&take_succ_i_exp);

        egraph.rebuild();
        splitter.case_split(&mut egraph, 1, &vec![], 1);
        assert!(egraph.colors().count() > 0);
        let found = splitter.find_splitters(&mut egraph);
        // egraph.filtered_dot(|eg, id| filterTypings(eg, id))
        //     .to_dot("take_succ_i.dot".to_string()).unwrap();
        assert_eq!(found.iter().filter(|x| x.color().is_some()).count(), 0, "Found splitters: {:?}", found);
    }
}
