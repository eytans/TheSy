use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use egg::{Pattern, RecExpr, Rewrite, Searcher, SymbolLang, Var};
use itertools::Itertools;
use thesy_parser::{grammar, ast};

use crate::lang::{DataType, Function};
use std::path::PathBuf;
use thesy_parser::ast::{Expression, Statement};
use thesy_parser::ast::Definitions::Defs;
use std::str::FromStr;
use crate::eggstentions::searchers::multisearcher::{MultiEqSearcher, MultiDiffSearcher, EitherSearcher, FilteringSearcher, ToDyn, aggregate_conditions};

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
        self.conjectures.extend_from_slice(&std::mem::take(&mut other.conjectures).into_iter()
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
        let res = grammar::DefsParser::new().parse(path.to_str().unwrap());
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

    fn exp_to_pattern(exp: Expression) -> Pattern<SymbolLang> {
        Pattern::from_str(&*exp.to_sexp_string()).unwrap()
    }

    fn make_rw(name: String, precond: Option<Expression>, source: Expression, target: Expression, conds: Vec<(thesy_parser::ast::Terminal, Expression)>) -> Rewrite<SymbolLang, ()> {
        let precond_searcher = precond.map(|e| {
            MultiEqSearcher::new(vec![Definitions::exp_to_pattern(e), Pattern::from_str("true").unwrap()])
        });
        let searcher = {
            let s = Definitions::exp_to_pattern(source);
            if precond.is_some() {
                MultiDiffSearcher::new(vec![
                    EitherSearcher::left(s),
                    EitherSearcher::right(precond_searcher.unwrap())
                ]).into_rc_dyn()
            } else {
                s.into_rc_dyn()
            }
        };
        let applier = Definitions::exp_to_pattern(target);
        let conditions = conds.into_iter().map(|(t, e)| {
            FilteringSearcher::create_non_pattern_filterer(Definitions::exp_to_pattern(e).into_rc_dyn(), Var::from_str(&*t.to_string()).unwrap())
        }).collect_vec();
        let cond_searcher = FilteringSearcher::new(searcher, aggregate_conditions(conditions));
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
                    match def {
                        ast::Rewrite::DRewrite(precond, source, target, conditions) => {
                            ;
                        }
                        ast::Rewrite::BRewrite(precond, source, target, conditions) => {}
                        ast::Rewrite::AddSearcher(precond, source, target, conditions) => {}
                    }
                }
                Statement::Function(_, _, _, _) => {}
                Statement::Datatype(_, _, _) => {}
                Statement::Goal(_, _, _) => {}
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