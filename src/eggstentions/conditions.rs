use egg::{Condition, EGraph, Var, Subst, Id, Language, Analysis};
use itertools::Itertools;


pub struct AndCondition<L: Language, N: Analysis<L>> {
    conditions: Vec<Box<dyn Condition<L, N>>>
}

impl<L: Language, N: Analysis<L>> AndCondition<L, N> {
    pub fn new(conditions: Vec<Box<dyn Condition<L, N>>>) -> AndCondition<L, N> {
        AndCondition{conditions}
    }
}

impl<L: Language, N: Analysis<L>> Condition<L, N> for AndCondition<L, N> {
    fn check(&self, egraph: &mut EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        self.conditions.iter().all(|c| c.check(egraph, eclass, subst))
    }

    fn vars(&self) -> Vec<Var> {
        self.conditions.iter().flat_map(|c| c.vars()).unique().collect_vec()
    }
}