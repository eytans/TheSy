use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use egg::{Pattern, RecExpr, Rewrite, Searcher, SymbolLang, Var};
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
use thesy_parser::ast::Terminal::Id;

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
                    Defs(stmts) => Definitions::from(stmts)
                }
            },
            Err(e) => {
                println!("{}", e);
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

    fn make_rw(name: String,
               precond: Option<Expression>,
               source: Expression,
               target: Expression,
               conds: Vec<(thesy_parser::ast::Terminal, Expression)>) -> Rewrite<SymbolLang, ()> {
        let (cond_searcher, applier) =
            Definitions::create_searcher_applier(precond, source, target, conds);
        Rewrite::new(name, cond_searcher, applier).unwrap()
    }
}

impl From<Vec<Statement>> for Definitions {
    fn from(x: Vec<Statement>) -> Self {
        let mut datatypes = vec![];
        let mut functions = vec![];
        let mut rws = vec![];
        let mut goals = vec![];
        for s in x {
            match s {
                Statement::RewriteDef(name, def) => {
                    Definitions::process_rw(&mut rws, name, def)
                }
                Statement::Function(
                    name, params, ret, body) => {
                    Definitions::process_fun(&mut functions, &mut rws, name, params, ret, body)
                }
                Statement::Datatype(name, type_params, constructors) => {
                    Definitions::process_datatype(&mut datatypes, name, constructors);
                }
                Statement::Goal(precond, exp1, exp2) => {
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
                    goals.push((type_map,
                                precond.map(|t|
                                                RecExpr::from_str(&*t.to_sexp_string()).unwrap()),
                                RecExpr::from_str(&*exp1.to_sexp_string()).unwrap(),
                                RecExpr::from_str(&*exp2.to_sexp_string()).unwrap()));
                }
            }
        }
        Definitions {
            datatypes,
            functions,
            rws,
            conjectures: goals,
            // TODO
            case_splitters: vec![]
        }
    }
}


impl std::fmt::Display for Definitions {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "datatypes:")?;
        for d in &self.datatypes {
            write!(f, "  ")?;
            d.fmt(f)?;
            writeln!(f);
        }
        writeln!(f, "functions:")?;
        for fun in &self.functions {
            write!(f, "  ")?;
            fun.fmt(f)?;
            writeln!(f);
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

impl Definitions {
    fn process_rw(rws: &mut Vec<Rewrite<SymbolLang, ()>>, name: String, def: ast::Rewrite) {
        match def {
            ast::Rewrite::DRewrite(
                precond, source, target, conds
            ) => {
                rws.push(Definitions::make_rw(name, precond, source, target, conds));
            }
            ast::Rewrite::BRewrite(
                precond, source, target, conds
            ) => {
                rws.push(Definitions::make_rw(name.clone(),
                                              precond.clone(),
                                              target.clone(),
                                              source.clone(),
                                              conds.clone()));
                rws.push(Definitions::make_rw(name, precond, source, target, conds));
            }
            ast::Rewrite::AddSearcher(
                precond, source, target, conds
            ) => {
                let (cond_searcher, applier) =
                    Definitions::create_searcher_applier(precond, source, target, conds);
                let diff_applier = DiffApplier::new(applier);
                rws.push(Rewrite::new(name, cond_searcher, diff_applier).unwrap());
            }
        }
    }

    fn process_datatype(datatypes: &mut Vec<DataType>, name: String, constructors: Vec<(String, Vec<(String, ast::Annotation)>)>) {
        let consts_funs = constructors.iter().map(|(name, params)| {
            let mut constr_params = params.iter()
                .map(|(_, anno)| RecExpr::from_str(
                    &*anno.get_type().unwrap().to_sexp_string())
                    .unwrap()).collect_vec();
            let ret = constr_params.pop().unwrap();
            Function::new(name.to_string(), constr_params, ret)
        }).collect_vec();
        datatypes.push(DataType::new(name, consts_funs));
    }

    fn process_fun(functions: &mut Vec<Function>, mut rws: &mut Vec<Rewrite<SymbolLang, ()>>, name: String, params: Vec<(String, Annotation)>, ret: Annotation, body: Option<Expression>) {
        let param_types = params.iter()
            .map(|(i, a)|
                RecExpr::from_str(&*a.get_type().unwrap().to_sexp_string()).unwrap()
            ).collect_vec();
        let ret_type = RecExpr::from_str(
            &*ret.get_type().unwrap().to_sexp_string()
        ).unwrap();
        functions.push(Function::new(name.clone(), param_types, ret_type));
        body.iter().for_each(|e| {
            let param_names = params.iter()
                .map(|(i, a)| "?".to_owned() + i).collect_vec();
            rws.extend(rewrite!(format!("{}_def", name);
                            {Pattern::from_str(&*format!("({} {})", name, param_names.join(" "))).unwrap()}
                            <=> {Pattern::from_str(&*e.to_sexp_string()).unwrap()}));
        })
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