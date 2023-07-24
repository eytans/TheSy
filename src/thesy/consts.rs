use egg::{SymbolLang, Pattern, Var, MultiPattern};
use egg::searchers::ToDyn;
use std::str::FromStr;
use crate::thesy::case_split::{CaseSplit, Split, SplitApplier};
use itertools::Itertools;
use crate::lang::{ThMultiPattern, ThRewrite};
use egg::multi_rewrite;

pub(crate) fn bool_rws() -> Vec<ThRewrite> {
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
        multi_rewrite!("and_implies"; "?m1 = (and ?x ?y), ?m1 = true" => "?x = true, ?y = true"),
        // and_implies2,

        rewrite!("not-true"; "(not true)" => "false"),
        rewrite!("not-false"; "(not false)" => "true"),

        multi_rewrite!("not-x-false"; "?m1 = (not ?x), ?m1 = false" => "?x = true"),
        multi_rewrite!("not-x-true"; "?m1 = (not ?x), ?m1 = true" => "?x = false"),
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

pub(crate) fn is_rws() -> Vec<ThRewrite> {
    vec![
        multi_rewrite!("is_cons_true"; "?m1 = (is-cons ?x), ?x = (cons ?y)" => "?m1 = true"),
        multi_rewrite!("is_cons_false"; "?m1 = (is-cons ?x), ?x = nil" => "?m1 = false"),
        multi_rewrite!("is_cons_conclusion"; "?m1 = (is-cons ?x), ?m1 = true" => "?m2 = (cons (isconsex ?x))"),
        multi_rewrite!("is_nil_conclusion"; "?m1 = (is-cons ?x), ?m1 = false" => "?x = nil"),
        multi_rewrite!("is_succ_true"; "?m1 = (is-succ ?x), ?x = (succ ?y)" => "?m1 = true"),
        rewrite!("is_succ_false"; "?m1 = (is-succ ?x), ?x = zero" => "?m1 = false"),
        rewrite!("is_ESC_true"; "?m1 = (is-ESC ?x), ?x = ESC" => "?m1 = true"),
    ]
}

pub(crate) fn equality_rws() -> Vec<ThRewrite> {
    vec![
        rewrite!("equality"; "(Eq ?x ?x)" => "true"),
        multi_rewrite!("equality-true"; "?m1 = (Eq ?x ?y), ?m1 = true" => "?x = ?y"),
        multi_rewrite!("equality-false-is-false"; "?m1 = (Eq ?x true), ?m1 = false" => "?x = false"),
        multi_rewrite!("equality-true-is-false"; "?m1 = (Eq ?x false), ?m1 = false" => "?x = true"),
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
    let ite_searcher: MultiPattern<SymbolLang> = "?root = (ite ?z ?x ?y), ?z != true, ?z != false".parse().unwrap();
    let mut res = CaseSplit::from_applier_patterns(vec![(ite_searcher.into_rc_dyn(), Pattern::from_str("?z").unwrap(), vec!["true".parse().unwrap(), "false".parse().unwrap()])]);
    let or_multi_searcher: ThMultiPattern = "?m1 = true, ?m1 = (or ?x ?y)".parse().unwrap();

    let x_var = Var::from_str("?x").unwrap();
    let y_var = Var::from_str("?y").unwrap();
    let m1_var = Var::from_str("?m1").unwrap();
    let or_implies_applier: SplitApplier = Box::new(move |_graph, sms| {
        sms.iter().flat_map(|sm| sm.substs.iter().filter_map(|subs|
            Some(Split::new(*subs.get(m1_var).unwrap(), vec![*subs.get(x_var).unwrap(), *subs.get(y_var).unwrap()], subs.color()))
        )).collect_vec()
    });

    res.extend(CaseSplit::new(vec![(or_multi_searcher.into_rc_dyn(), or_implies_applier)]));
    res
}