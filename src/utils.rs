use crate::lang::{ThEGraph, ThExpr};
use egg::{EGraph, Id, Language, MultiPattern, Pattern, PatternAst, RecExpr, Rewrite, Searcher, SymbolLang, Var};
use std::collections::HashSet;
use std::ops::Deref;
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use crate::thesy::case_split::CaseSplitStats;
use crate::thesy::TheSy;

lazy_static! {
    static ref TRUE_AST: PatternAst<SymbolLang> = Pattern::from_str("true").unwrap().ast;
    static ref FALSE_AST: PatternAst<SymbolLang> = Pattern::from_str("false").unwrap().ast;
    static ref MULTIPATTERN_VAR_COUNTER: AtomicUsize = AtomicUsize::default();
}

pub fn fresh_multipattern_var() -> Var {
    let i = MULTIPATTERN_VAR_COUNTER.fetch_add(1, Ordering::SeqCst);
    format!("?__multipattern_var_{}", i).parse().unwrap()
}

pub fn pattern_ast_is_true(p: Pattern<SymbolLang>) -> Vec<(Var, PatternAst<SymbolLang>)> {
    let var = fresh_multipattern_var();
    vec![(var, TRUE_AST.clone()), (var, p.ast)]
}

pub fn pattern_is_true(p: Pattern<SymbolLang>) -> (Var, MultiPattern<SymbolLang>) {
    let vec = pattern_ast_is_true(p);
    let var = vec[0].0;
    (var, MultiPattern::new(vec))
}

pub fn pattern_is_false(p: Pattern<SymbolLang>) -> (Var, MultiPattern<SymbolLang>) {
    let var = fresh_multipattern_var();
    (var, MultiPattern::new(vec![(var, p.ast), (var, FALSE_AST.clone())]))
}

#[allow(dead_code)]
pub fn filterTypings(egraph: &ThEGraph, id: Id) -> bool {
    // Return true if eclass has typed node, or is the in index 1 of a typed node.
    let node = SymbolLang::from_op_str("typed", vec![]).unwrap();
    let res = !egraph
        .classes_by_op_id()
        .get(&node.op_id())
        .map_or(false, |x| x.contains(&id));
    // Now check if it is the second argument of a typed node.
    let x = "?x".parse().unwrap();
    let searcher: Pattern<SymbolLang> = "(typed ?y ?x)".parse().unwrap();
    let matched: HashSet<Id> = searcher
        .search(egraph).map(|sm| sm.substs().map(|s| *s.get(x).unwrap()).collect()).unwrap_or_default();
    return res && !matched.contains(&id);
}

pub fn create_graph(expressions: &[impl Deref<Target = ThExpr>]) -> ThEGraph {
    let mut orig_egraph: ThEGraph = EGraph::default();
    for e in expressions {
        let _ = orig_egraph.add_expr(e);
    }
    orig_egraph.rebuild();
    orig_egraph
}


pub fn add_assumption(orig_egraph: &mut ThEGraph, pre: &ThExpr) {
    let precond_id = orig_egraph.add_expr(pre);
    let true_id = orig_egraph.add_expr(&RecExpr::from_str("true").unwrap());
    orig_egraph.union(precond_id, true_id);
    orig_egraph.add(SymbolLang::new("=", vec![precond_id, true_id]));
}

pub struct TheSyRunRes {
    pub thesy: TheSy,
    #[allow(dead_code)]
    pub rws: Vec<Rewrite<SymbolLang, ()>>,
    #[allow(dead_code)]
    pub success: bool,
    pub case_split_stats: CaseSplitStats,
}

impl TheSyRunRes {
    pub fn new(thesy: TheSy, rws: Vec<Rewrite<SymbolLang, ()>>, success: bool, case_split_stats: CaseSplitStats) -> Self {
        Self { thesy, rws, success, case_split_stats }
    }
}


#[cfg(test)]
mod test {
    use egg::RecExpr;

    use crate::{lang::{ThEGraph, ThNode}, utils::filterTypings, TheSyConfig, thesy::TheSy};
    use crate::utils::fresh_multipattern_var;

    #[test]
    fn test_filter_typings() {
        let mut egraph = ThEGraph::default();
        let x: RecExpr<ThNode> = "x".parse().unwrap();
        let y: RecExpr<ThNode> = "y".parse().unwrap();
        let typed: RecExpr<ThNode> = "(typed x y)".parse().unwrap();
        let id1 = egraph.add_expr(&x);
        let id2 = egraph.add_expr(&y);
        let id3 = egraph.add_expr(&typed);
        egraph.rebuild();
        assert!(filterTypings(&egraph, id1));
        assert!(!filterTypings(&egraph, id2));
        assert!(!filterTypings(&egraph, id3));
    }

    #[test]
    fn test_filter_typings_on_thesy() {
        let config = TheSyConfig::from_path("theories/list.th".parse().unwrap());
        let mut thesy = TheSy::from(&config);
        thesy.increase_depth();
        thesy.egraph.rebuild();
        let dot_str = thesy.egraph.dot().to_string();
        thesy.egraph.dot().to_dot("test.dot").unwrap();
        let filtered_dot_str = thesy.egraph.filtered_dot(filterTypings).to_string();
        assert!(dot_str.contains("\"Lst\""));
        assert!(!filtered_dot_str.contains("\"Lst\""));
    }

    #[test]
    fn fresh_var_is_fresh() {
        let x1 = fresh_multipattern_var();
        let x2 = fresh_multipattern_var();
        assert_ne!(x1, x2);
    }
}
