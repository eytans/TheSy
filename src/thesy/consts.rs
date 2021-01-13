use egg::{Rewrite, SymbolLang, Pattern, Var, EGraph, Subst, Id, SearchMatches, Searcher};
use crate::eggstentions::searchers::multisearcher::{MultiEqSearcher, FilteringSearcher, aggregate_conditions, ToDyn};
use crate::eggstentions::appliers::{DiffApplier, UnionApplier};
use std::str::FromStr;
use crate::thesy::{case_split, TheSy, Examples};
use crate::thesy::case_split::{CaseSplit, Split, SplitAdapter, MultiPatternAdapter};
use itertools::Itertools;
use std::rc::Rc;

pub(crate) fn bool_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    let and_multi_searcher = MultiEqSearcher::new(vec![
        Pattern::from_str("true").unwrap(),
        Pattern::from_str("(and ?x ?y)").unwrap(),
    ]);

    let and_implies = rewrite!("and_implies"; {and_multi_searcher.clone()} => "(= ?x true)");
    let and_implies2 = rewrite!("and_implies2"; {and_multi_searcher} => "(= ?y true)");

    vec![
        rewrite!("or-true"; "(or true ?x)" => "true"),
        rewrite!("or-true2"; "(or ?x true)" => "true"),
        rewrite!("or-false"; "(or false ?x)" => "?x"),
        rewrite!("or-false2"; "(or ?x false)" => "?x"),
        // or_implies,

        rewrite!("and-true"; "(and true ?x)" => "?x"),
        rewrite!("and-true2"; "(and ?x true)" => "?x"),
        rewrite!("and-false"; "(and false ?x)" => "false"),
        rewrite!("and-false2"; "(and ?x false)" => "false"),
        // and_implies,
        // and_implies2,

        rewrite!("not-true"; "(not true)" => "false"),
        rewrite!("not-false"; "(not false)" => "true"),
    ]
}

// Also common that less is skipped
pub(crate) fn less_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    vec![
        rewrite!("less-zero"; "(less ?x zero)" => "false"),
        rewrite!("less-zs"; "(less zero (succ ?x))" => "true"),
        rewrite!("less-succ"; "(less (succ ?y) (succ ?x))" => "(less ?y ?x)")
    ]
}

fn cons_conc_searcher() -> MultiEqSearcher<Pattern<SymbolLang>> {
    MultiEqSearcher::new(vec!["true".parse().unwrap(), "(is-cons ?x)".parse().unwrap()])
}

fn cons_conclusion() -> DiffApplier<Pattern<SymbolLang>> {
    DiffApplier::new("(cons (isconsex ?x))".parse().unwrap())
}

pub(crate) fn is_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    vec![
        rewrite!("is_cons_true"; {FilteringSearcher::from(Pattern::from_str("(is-cons ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("(cons ?y)".parse::<Pattern<SymbolLang>>().unwrap().into_rc_dyn(), Var::from_str("?x").unwrap()))} => "true"),
        rewrite!("is_cons_false"; {FilteringSearcher::from(Pattern::from_str("(is-cons ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("nil".parse::<Pattern<SymbolLang>>().unwrap().into_rc_dyn(), Var::from_str("?x").unwrap()))} => "false"),
        rewrite!("is_cons_conclusion"; {cons_conc_searcher()} => {cons_conclusion()}),
        rewrite!("is_succ_true"; {FilteringSearcher::from(Pattern::from_str("(is-succ ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("(succ ?y)".parse::<Pattern<SymbolLang>>().unwrap().into_rc_dyn(), Var::from_str("?x").unwrap()))} => "true"),
        rewrite!("is_succ_false"; {FilteringSearcher::from(Pattern::from_str("(is-succ ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("zero".parse::<Pattern<SymbolLang>>().unwrap().into_rc_dyn(), Var::from_str("?x").unwrap()))} => "false"),
        rewrite!("is_ESC_true"; {FilteringSearcher::from(Pattern::from_str("(is-ESC ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("ESC".parse::<Pattern<SymbolLang>>().unwrap().into_rc_dyn(), "?x".parse().unwrap()))} => "true"),
    ]
}

pub(crate) fn equality_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    let eq_searcher = MultiEqSearcher::new(vec![Pattern::from_str("true").unwrap(), Pattern::from_str("(= ?x ?y)").unwrap()]);
    let union_applier = UnionApplier::new(vec![Var::from_str("?x").unwrap(), Var::from_str("?y").unwrap()]);
    vec![
        rewrite!("equality"; "(= ?x ?x)" => "true"),
        rewrite!("equality-true"; eq_searcher => union_applier),
        // TODO: I would like to split by equality but not a possibility with current conditions.
        // rewrite!("equality-split"; "(= ?x ?y)" => "(potential_split (= ?x ?y) true false)" if {NonPatternCondition::new(Pattern::from_str("").unwrap(), Var::from_str("?"))})
    ]
}

pub(crate) fn ite_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    vec![
        rewrite!("ite_true"; "(ite true ?x ?y)" => "?x"),
        rewrite!("ite_false"; "(ite false ?x ?y)" => "?y"),
    ]
}

struct OrSplitAdapter {
    searcher: MultiEqSearcher<Pattern<SymbolLang>>,
    x_var: Var,
    y_var: Var
}

impl OrSplitAdapter {
    pub fn new() -> Self {
        let searcher = MultiEqSearcher::new(vec![
            Pattern::from_str("true").unwrap(),
            Pattern::from_str("(or ?x ?y)").unwrap(),
        ]);
        let x_var = Var::from_str("?x").unwrap();
        let y_var = Var::from_str("?y").unwrap();
        OrSplitAdapter{searcher, x_var, y_var}
    }
}

impl SplitAdapter for OrSplitAdapter {
    fn search(&self, egraph: &EGraph<SymbolLang, ()>) -> Vec<SearchMatches> {
        self.searcher.search(egraph)
    }

    fn apply(&self, graph: &mut EGraph<SymbolLang, ()>, search_matches: Vec<SearchMatches>, id_map: Vec<Vec<Id>>) -> Vec<Split> {
        let true_root = graph.add_expr(&"true".parse().unwrap());
        search_matches.iter().flat_map(|sm| sm.substs.iter().map(|subs|
            Split::new(true_root, vec![*subs.get(self.x_var).unwrap(), *subs.get(self.y_var).unwrap()])
        )).collect_vec()
    }

    fn add_match_pattern(&self, graph: &mut EGraph<SymbolLang, ()>, subst: Subst) -> Id {
        unimplemented!()
    }
}

pub fn system_case_splits(examples: Vec<Examples>) -> CaseSplit {
    let searcher: Pattern<SymbolLang> = Pattern::from_str("(ite ?z ?x ?y)").unwrap();
    let ite_searcher = {
        let true_cond = FilteringSearcher::create_non_pattern_filterer(Pattern::from_str("true").unwrap().into_rc_dyn(), Var::from_str("?z").unwrap());
        let false_cond = FilteringSearcher::create_non_pattern_filterer(Pattern::from_str("false").unwrap().into_rc_dyn(), Var::from_str("?z").unwrap());
        FilteringSearcher::new(searcher.into_rc_dyn(), aggregate_conditions::<SymbolLang, ()>(vec![true_cond, false_cond]))
    };
    let ite_adapter = MultiPatternAdapter::new(ite_searcher.into_rc_dyn(), Box::new(searcher), Var::from_str("?z").unwrap(), vec!["true".parse().unwrap(), "false".parse().unwrap()]);
    CaseSplit::new(vec![Rc::new(OrSplitAdapter::new()), Rc::new(ite_adapter)])
}