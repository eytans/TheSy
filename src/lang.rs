use egg::{EGraph, Id, Language, MultiPattern, Pattern, RecExpr, Rewrite, Symbol, SymbolLang};
use itertools::Itertools;
use serde::{Deserialize, Serialize};

use egg::expression_ops::{IntoTree, Tree};
use std::fmt::{Display, Formatter};
use crate::PRETTY_W;

pub type ThNode = SymbolLang;
pub type ThAnl = ();
pub type ThExpr = RecExpr<ThNode>;
#[allow(dead_code)]
pub type ThPattern = Pattern<ThNode>;
pub type ThEGraph = EGraph<ThNode, ThAnl>;
pub type ThRewrite = Rewrite<ThNode, ThAnl>;
pub type ThMultiPattern = MultiPattern<ThNode>;

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct DataType {
    pub name: String,
    pub type_params: Vec<ThExpr>,
    // TODO: change to Function instead of rec expr
    /// Constructor name applied on types
    pub constructors: Vec<Function>,
}

impl Display for DataType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Datatype {}: types - {}",
                 self.name, self.type_params.iter().map(|e| e.pretty(PRETTY_W)).join(" "))?;
        write!(f, "  {}", self.constructors.iter().map(|f| format!("{}", f)).join("| "))
    }
}

#[derive(Clone, Hash, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub params: Vec<ThExpr>,
    /// Constructor name applied on types
    pub ret_type: ThExpr,
}

impl Display for Function {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Function {}: {}{}{}",
            self.name,
            self.params.iter().map(|x| x.pretty(PRETTY_W)).join(" -> "),
            self.params.first().map(|_x| " -> ").unwrap_or(" "),
            self.ret_type.pretty(PRETTY_W)
        )
    }
}

impl Function {
    pub fn new(name: String, params: Vec<ThExpr>, ret_type: ThExpr) -> Function {
        Function { name, params, ret_type }
    }

    pub fn as_exp(&self) -> ThExpr {
        let as_type = self.get_type();
        let mut children = as_type.as_ref().iter().cloned().dropping_back(1).collect_vec();
        let mut new_last = as_type.as_ref().last().unwrap().clone();
        new_last.op = Symbol::from(self.name.clone());
        children.push(new_last);
        RecExpr::from(children)
    }

    pub fn get_type(&self) -> ThExpr {
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

    pub fn apply_params(&self, params: Vec<ThExpr>) -> ThExpr {
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

impl From<ThExpr> for Function {
    fn from(exp: ThExpr) -> Self {
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

    pub fn generic(name: String, type_params: Vec<ThExpr>, constructors: Vec<Function>) -> DataType {
        DataType { name, type_params, constructors }
    }

    pub fn as_exp(&self) -> ThExpr {
        let mut res = vec![];
        let children = self.type_params.iter().map(|e| {
            res.extend(e.as_ref().iter().cloned());
            Id::from(res.len() - 1)
        }).collect_vec();
        res.push(SymbolLang::new(self.name.clone(), children));
        RecExpr::from(res)
    }
}