use egg::{ImmutableCondition, Condition, EGraph, Var, Subst, Id, Language, Analysis, RcImmutableCondition, ToCondRc};
use itertools::Itertools;
use std::fmt::Formatter;
use std::rc::Rc;

pub struct AndCondition<L: Language, N: Analysis<L>> {
    conditions: Vec<RcImmutableCondition<L, N>>
}

impl<L: Language, N: Analysis<L>> AndCondition<L, N> {
    pub fn new(conditions: Vec<RcImmutableCondition<L, N>>) -> AndCondition<L, N> {
        AndCondition {conditions}
    }
}

impl<L: Language, N: Analysis<L>> ToCondRc<L, N> for AndCondition<L, N> {}

impl<L: Language, N: Analysis<L>> ImmutableCondition<L, N> for AndCondition<L, N> {
    fn check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        self.conditions.iter().all(|c| c.check_imm(egraph, eclass, subst))
    }

    fn vars(&self) -> Vec<Var> {
        self.conditions.iter().flat_map(|c| c.vars()).unique().collect_vec()
    }

    fn describe(&self) -> String {
        format!("{}", self.conditions.iter().map(|x| x.describe()).join(" && "))
    }
}

pub struct OrCondition<L: Language, N: Analysis<L>> {
    conditions: Vec<RcImmutableCondition<L, N>>
}

impl<L: Language, N: Analysis<L>> OrCondition<L, N> {
    pub fn new(conditions: Vec<RcImmutableCondition<L, N>>) -> OrCondition<L, N> {
        OrCondition {conditions}
    }
}

impl<L: Language, N: Analysis<L>> ToCondRc<L, N> for OrCondition<L, N> {}

impl<L: Language, N: Analysis<L>> ImmutableCondition<L, N> for OrCondition<L, N> {
    fn check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        self.conditions.is_empty() || self.conditions.iter()
            .any(|c| c.check_imm(egraph, eclass, subst))
    }

    fn vars(&self) -> Vec<Var> {
        self.conditions.iter().flat_map(|c| c.vars()).unique().collect_vec()
    }

    fn describe(&self) -> String {
        format!("{}", self.conditions.iter().map(|x| x.describe()).join(" || "))
    }
}
