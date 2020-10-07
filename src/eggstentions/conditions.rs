use egg::{Pattern, SymbolLang, Condition, EGraph, Var, Subst, Id, Searcher, Language, Analysis};
use smallvec::alloc::str::FromStr;
use itertools::Itertools;

pub struct NonPatternCondition {
    pattern: Pattern<SymbolLang>,
    root: Var
}

impl NonPatternCondition {
    pub fn new(pattern: Pattern<SymbolLang>, root: Var) -> NonPatternCondition {
        NonPatternCondition{pattern, root}
    }
}

impl Condition<SymbolLang, ()> for NonPatternCondition {
    fn check(&self, egraph: &mut EGraph<SymbolLang, ()>, eclass: Id, subst: &Subst) -> bool {
        self.pattern.search_eclass(egraph, *subst.get(self.root).unwrap()).is_none()
    }

    fn vars(&self) -> Vec<Var> {
        vec![self.root]
    }
}

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