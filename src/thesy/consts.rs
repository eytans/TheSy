use egg::{Rewrite, SymbolLang, Pattern, Var, ConditionalApplier};
use crate::eggstentions::multisearcher::multisearcher::MultiEqSearcher;
use crate::eggstentions::appliers::{DiffApplier, UnionApplier};
use std::str::FromStr;
use crate::eggstentions::conditions::{NonPatternCondition, AndCondition, PatternCondition};
use crate::thesy::case_split;

pub(crate) fn bool_rws() -> Vec<Rewrite<SymbolLang, ()>> {
    let or_multi_searcher = MultiEqSearcher::new(vec![
        Pattern::from_str("true").unwrap(),
        Pattern::from_str("(or ?x ?y)").unwrap(),
    ]);
    let or_implies_applier: Pattern<SymbolLang> = format!("({} true ?x ?y)", case_split::SPLITTER).parse().unwrap();
    let or_implies = rewrite!("or_implies"; or_multi_searcher => or_implies_applier);

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
        or_implies,

        rewrite!("and-true"; "(and true ?x)" => "?x"),
        rewrite!("and-true2"; "(and ?x true)" => "?x"),
        rewrite!("and-false"; "(and false ?x)" => "false"),
        rewrite!("and-false2"; "(and ?x false)" => "false"),
        and_implies,
        and_implies2,

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
        rewrite!("is_cons_true"; "(is-cons ?x)" => "true" if PatternCondition::new("(cons ?y)".parse().unwrap(), Var::from_str("?x").unwrap())),
        rewrite!("is_cons_false"; "(is-cons ?x)" => "false" if PatternCondition::new("nil".parse().unwrap(), Var::from_str("?x").unwrap())),
        rewrite!("is_cons_conclusion"; {cons_conc_searcher()} => {cons_conclusion()}),
        rewrite!("is_succ_true"; "(is-succ ?x)" => "true" if PatternCondition::new("(succ ?y)".parse().unwrap(), "?x".parse().unwrap())),
        rewrite!("is_succ_false"; "(is-succ ?x)" => "false" if PatternCondition::new("zero".parse().unwrap(), "?x".parse().unwrap())),
        rewrite!("is_ESC_true"; "(is-ESC ?x)" => "true" if PatternCondition::new("ESC".parse().unwrap(), "?x".parse().unwrap())),
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
    let potential_split_conc = format!("({} ?z true false)", case_split::SPLITTER);
    let applier: Pattern<SymbolLang> = potential_split_conc.parse().unwrap();
    let true_cond = NonPatternCondition::new(Pattern::from_str("true").unwrap(), Var::from_str("?z").unwrap());
    let false_cond = NonPatternCondition::new(Pattern::from_str("false").unwrap(), Var::from_str("?z").unwrap());
    let cond_applier = ConditionalApplier { applier, condition: AndCondition::new(vec![Box::new(true_cond), Box::new(false_cond)]) };
    let split = Rewrite::new("ite_split",
                             Pattern::from_str("(ite ?z ?x ?y)").unwrap(),
                             DiffApplier::new(cond_applier)).unwrap();
    vec![
        rewrite!("ite_true"; "(ite true ?x ?y)" => "?x"),
        rewrite!("ite_false"; "(ite false ?x ?y)" => "?y"),
        split
    ]
}