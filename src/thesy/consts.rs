use egg::{Rewrite, SymbolLang, Pattern, Var, Language, Id, RcImmutableCondition, ToCondRc, OpId, Symbol};
use egg::searchers::{FilteringSearcher, MultiDiffSearcher, ToDyn};
use egg::appliers::{DiffApplier, UnionApplier};
use std::str::FromStr;
use crate::thesy::{case_split, TheSy};
use crate::thesy::case_split::{CaseSplit, Split, SplitApplier};
use itertools::Itertools;
use std::rc::Rc;
use egg::conditions::AndCondition;
use egg::searchers::{MatcherContainsCondition, PatternMatcher, ToRc, VarMatcher};
use crate::lang::ThRewrite;

pub(crate) fn bool_rws() -> Vec<ThRewrite> {
    let and_multi_searcher = {
        let p: Pattern<SymbolLang> = "(and ?x ?y)".parse().unwrap();
        FilteringSearcher::searcher_is_true(p)
    };

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
pub(crate) fn less_rws() -> Vec<ThRewrite> {
    vec![
        rewrite!("less-zero"; "(less ?x zero)" => "false"),
        rewrite!("less-zs"; "(less zero (succ ?x))" => "true"),
        rewrite!("less-succ"; "(less (succ ?y) (succ ?x))" => "(less ?y ?x)"),
    ]
}

fn cons_conc_searcher() -> FilteringSearcher<SymbolLang, ()> {
    FilteringSearcher::searcher_is_true("(is-cons ?x)".parse::<Pattern<SymbolLang>>().unwrap())
}

fn cons_conclusion() -> DiffApplier<Pattern<SymbolLang>> {
    DiffApplier::new("(cons (isconsex ?x))".parse().unwrap())
}

pub(crate) fn is_rws() -> Vec<ThRewrite> {
    vec![
        rewrite!("is_cons_true"; {FilteringSearcher::from(Pattern::from_str("(is-cons ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("(cons ?y)".parse::<Pattern<SymbolLang>>().unwrap()))} => "true"),
        rewrite!("is_cons_false"; {FilteringSearcher::from(Pattern::from_str("(is-cons ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("nil".parse::<Pattern<SymbolLang>>().unwrap()))} => "false"),
        rewrite!("is_cons_conclusion"; {cons_conc_searcher()} => {cons_conclusion()}),
        rewrite!("is_succ_true"; {FilteringSearcher::from(Pattern::from_str("(is-succ ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("(succ ?y)".parse::<Pattern<SymbolLang>>().unwrap()))} => "true"),
        rewrite!("is_succ_false"; {FilteringSearcher::from(Pattern::from_str("(is-succ ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("zero".parse::<Pattern<SymbolLang>>().unwrap()))} => "false"),
        rewrite!("is_ESC_true"; {FilteringSearcher::from(Pattern::from_str("(is-ESC ?x)").unwrap(), FilteringSearcher::create_exists_pattern_filterer("ESC".parse::<Pattern<SymbolLang>>().unwrap()))} => "true"),
    ]
}

pub(crate) fn equality_rws() -> Vec<ThRewrite> {
    let eq_searcher = FilteringSearcher::searcher_is_true(Pattern::from_str("(= ?x ?y)").unwrap());
    let union_applier = UnionApplier::new(vec![Var::from_str("?x").unwrap(), Var::from_str("?y").unwrap()]);
    vec![
        rewrite!("equality"; "(= ?x ?x)" => "true"),
        rewrite!("equality-true"; eq_searcher => union_applier),
        // TODO: I would like to split by equality but not a possibility with current conditions.
        // rewrite!("equality-split"; "(= ?x ?y)" => "(potential_split (= ?x ?y) true false)" if {NonPatternCondition::new(Pattern::from_str("").unwrap(), Var::from_str("?"))})
    ]
}

pub(crate) fn ite_rws() -> Vec<ThRewrite> {
    vec![
        rewrite!("ite_true"; "(ite true ?x ?y)" => "?x"),
        rewrite!("ite_false"; "(ite false ?x ?y)" => "?y"),
    ]
}

pub fn system_case_splits() -> CaseSplit {
    let ite_searcher = {
        let searcher: Pattern<SymbolLang> = Pattern::from_str("(ite ?z ?x ?y)").unwrap();
        let true_cond = FilteringSearcher::<SymbolLang, ()>::create_non_pattern_filterer(
            VarMatcher::new(Var::from_str("?z").unwrap()).into_rc(),
            PatternMatcher::new("true".parse().unwrap()).into_rc());
        let false_cond = FilteringSearcher::<SymbolLang, ()>::create_non_pattern_filterer(
            VarMatcher::new(Var::from_str("?z").unwrap()).into_rc(),
            PatternMatcher::new("false".parse().unwrap()).into_rc());
        FilteringSearcher::new(searcher.into_rc_dyn(),
            AndCondition::<SymbolLang, ()>::new(vec![true_cond, false_cond]).into_rc())
    };
    let mut res = CaseSplit::from_applier_patterns(vec![(ite_searcher.into_rc_dyn(), Pattern::from_str("?z").unwrap(), vec!["true".parse().unwrap(), "false".parse().unwrap()])]);

    let or_multi_searcher = FilteringSearcher::searcher_is_true(Pattern::from_str("(or ?x ?y)").unwrap());

    let x_var = Var::from_str("?x").unwrap();
    let y_var = Var::from_str("?y").unwrap();
    let or_implies_applier: SplitApplier = Box::new(move |graph, sms| {
        let true_root = graph.add_expr(&"true".parse().unwrap());
        sms.iter().flat_map(|sm| sm.substs.iter().filter_map(|subs|
            Some(Split::new(true_root, vec![*subs.get(x_var).unwrap(), *subs.get(y_var).unwrap()], subs.color()))
        )).collect_vec()
    });

    res.extend(CaseSplit::new(vec![(or_multi_searcher.into_rc_dyn(), or_implies_applier)]));
    res
}