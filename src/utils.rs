use crate::lang::{ThEGraph, ThExpr};
use egg::expression_ops::{IntoTree, RecExpSlice, Tree};
use egg::{Analysis, ColorId, EGraph, ENodeOrVar, Id, ImmutableCondition, Language, MultiPattern, Pattern, PatternAst, RecExpr, Rewrite, Searcher, Subst, SymbolLang, ToCondRc, Var};
use indexmap::IndexSet;
use itertools::Itertools;
use std::collections::HashSet;
use std::iter::FromIterator;
use std::ops::Deref;
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use thesy_parser::ast::Expression;
use crate::thesy::case_split::CaseSplitStats;
use crate::thesy::TheSy;

/**
* [orig] is the expression of the `Subst` in [check_imm].
*/
#[derive(Clone, Debug)]
pub struct SubPattern<L: Language> {
    orig: Expression,
    pub patterns: Vec<(Var, Pattern<L>)>,
}

impl<L: Language> SubPattern<L> {
    fn collect_patterns(
        orig: &Expression,
        pattern_tree: &RecExpSlice<ENodeOrVar<L>>,
    ) -> Result<Vec<(Var, Pattern<L>)>, String> {
        let mut res = Vec::new();
        // For each node in the orig pattern we will check the new pattern.
        //  1. If orig and new pattern are nodes assert they agree, otherwise error.
        if orig.root().is_id() && pattern_tree.is_root_ident() {
            if orig.children().len() != pattern_tree.children().len()
                || orig.root().ident() != &pattern_tree.root().display_op().to_string()
            {
                return Err(format!(
                    "Patterns don't agree: {}{} != {}{}",
                    orig.root().ident(),
                    orig.children().len(),
                    pattern_tree.root().display_op(),
                    pattern_tree.children().len()
                ));
            }
            for (orig_child, pattern_child) in
                orig.children().iter().zip(pattern_tree.children().iter())
            {
                res.extend(SubPattern::collect_patterns(orig_child, pattern_child)?);
            }
        }
        //  2. If orig is node and new pattern is a hole then skip this is a constant derived
        //      from the orig pattern substitution and there is no need to search this.
        else if orig.root().is_id() && pattern_tree.is_root_hole() {
            // Do nothing
        }
        //  3. If the orig is a hole and new pattern is a node, add a subpattern that should be
        //     started from the eclasses the orig hole recieves.
        else if orig.root().is_hole() && pattern_tree.is_root_ident() {
            let pattern_root = Var::from_str(&*orig.root().to_string()).unwrap();
            res.push((pattern_root, Pattern::from(pattern_tree.to_clean_exp())));
        }
        // 4. If the orig is a hole and new pattern is a hole, assert holes are equal
        else if orig.root().is_hole() && pattern_tree.is_root_hole() {
            if orig.root().to_string()
                == pattern_tree
                    .root()
                    .display_op()
                    .to_string()
                    .replace("?", "")
            {
                return Err(format!(
                    "Patterns don't agree: {} != {}",
                    orig.root().ident(),
                    pattern_tree.root().display_op()
                ));
            }
        }
        Ok(res)
    }

    pub fn new(orig: Expression, pattern: Pattern<L>) -> Self {
        let pattern_tree = pattern.ast.into_tree();
        debug_assert_eq!(
            orig.root().ident(),
            &pattern_tree.root().display_op().to_string()
        );
        let patterns = Self::collect_patterns(&orig, &pattern_tree);
        patterns
            .map(|p| SubPattern { orig, patterns: p })
            .unwrap_or_else(|e| panic!("{}", e))
    }
}

impl<L: Language, N: Analysis<L>> ToCondRc<L, N> for SubPattern<L> {}

impl<L: Language, N: Analysis<L>> ImmutableCondition<L, N> for SubPattern<L> {
    fn check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        trace!(
            "SubPattern::{}({}, {}) - Start",
            ImmutableCondition::<L, N>::describe(self),
            eclass,
            subst
        );
        let colores = self.colored_check_imm(egraph, eclass, subst);
        let res = if colores.is_none() {
            false
        } else if colores.as_ref().unwrap().is_empty() {
            true
        } else {
            subst.color().is_some() && colores.unwrap().contains(&subst.color().unwrap())
        };
        trace!(
            "SubPattern::{}({}, {}) - End: {}",
            ImmutableCondition::<L, N>::describe(self),
            eclass,
            subst,
            res
        );
        res
    }

    fn colored_check_imm(
        &self,
        egraph: &EGraph<L, N>,
        eclass: Id,
        subst: &Subst,
    ) -> Option<Vec<ColorId>> {
        // Same as check_imm but collects colors to use when comparing vars for each pattern.
        // If no patterns in self then it is true always (i.e. returns black).
        trace!(
            "SubPattern::colored::{}({}, {}) - Start",
            ImmutableCondition::<L, N>::describe(self),
            eclass,
            subst
        );
        let mut res = vec![];
        'patterns: for (var, pattern) in &self.patterns {
            // Get eclass from the substitution
            let eclass = subst
                .get(var.clone())
                .unwrap_or_else(|| panic!("{} not found in {}", var, subst));
            let subs = if let Some(c) = subst.color() {
                pattern.colored_search_eclass(egraph, *eclass, c)
            } else {
                pattern.search_eclass(egraph, *eclass)
            };
            if subs.is_none() {
                trace!(
                    "SubPattern::colored::{}({}, {}) - End: None",
                    ImmutableCondition::<L, N>::describe(self),
                    eclass,
                    subst
                );
                return None;
            }

            // Check if pattern vars matter
            let vars = pattern
                .vars()
                .iter()
                .copied()
                .filter(|v| subst.get(*v).is_some())
                .collect_vec();
            if vars.is_empty() {
                continue 'patterns;
            }

            // If black continue outer loop.
            // If it is not black, collect/update possible colors in res using what is found in
            // pattern_colors.
            let mut pattern_colors: IndexSet<ColorId> = Default::default();
            for s in subs.unwrap().substs {
                let mut not_equal_vars = vars
                    .iter()
                    .filter(|v| {
                        let v = **v;
                        debug_assert_eq!(
                            egraph.opt_colored_find(s.color(), *s.get(v).unwrap()),
                            *s.get(v).unwrap()
                        );
                        debug_assert_eq!(
                            egraph.opt_colored_find(subst.color(), *subst.get(v).unwrap()),
                            *subst.get(v).unwrap()
                        );
                        s.get(v) != subst.get(v)
                    })
                    .copied()
                    .collect_vec();
                if not_equal_vars.is_empty() {
                    continue 'patterns;
                }
                // In the future if we support #hierarcal_colors we should not return here.
                if s.color().is_some() {
                    trace!(
                        "SubPattern::colored::{}({}, {}) - End: None",
                        ImmutableCondition::<L, N>::describe(self),
                        eclass,
                        subst
                    );
                    return None;
                }

                let colored_equalities_for_var = |v: Var| {
                    egraph
                        .get_colored_equalities(*s.get(v).unwrap())
                        .map(|x| {
                            x.into_iter()
                                .filter(|(c_id, id)| {
                                    *id == egraph
                                        .opt_colored_find(Some(*c_id), *subst.get(v).unwrap())
                                })
                                .map(|(c_id, _)| c_id)
                                .collect_vec()
                        })
                        .unwrap_or_default()
                };
                // We need to recalculate all agree, but consider colored equalities.
                let mut working_colors: IndexSet<ColorId> = IndexSet::from_iter({
                    colored_equalities_for_var(not_equal_vars.pop().unwrap()).into_iter()
                });
                if working_colors.is_empty() {
                    trace!(
                        "SubPattern::colored::{}({}, {}) - End: None",
                        ImmutableCondition::<L, N>::describe(self),
                        eclass,
                        subst
                    );
                    return None;
                }
                for v in not_equal_vars {
                    let colors: IndexSet<ColorId> =
                        IndexSet::from_iter(colored_equalities_for_var(v).into_iter());
                    working_colors = working_colors.intersection(&colors).copied().collect();
                    if working_colors.is_empty() {
                        trace!(
                            "SubPattern::colored::{}({}, {}) - End: None",
                            ImmutableCondition::<L, N>::describe(self),
                            eclass,
                            subst
                        );
                        return None;
                    }
                }
                pattern_colors.extend(working_colors);
            }
            // If we got here then no subst matched the pattern in black/orig_color.
            if res.is_empty() {
                res = pattern_colors.into_iter().collect_vec();
            } else {
                res.retain(|c| pattern_colors.contains(c));
                if res.is_empty() {
                    trace!(
                        "SubPattern::colored::{}({}, {}) - End: None",
                        ImmutableCondition::<L, N>::describe(self),
                        eclass,
                        subst
                    );
                    return None;
                }
            }
        }
        trace!(
            "SubPattern::colored::{}({}, {}) - End: {:?}",
            ImmutableCondition::<L, N>::describe(self),
            eclass,
            subst,
            res
        );
        Some(res)
    }

    fn describe(&self) -> String {
        format!(
            "{} -> {}",
            self.patterns
                .iter()
                .map(|(v, p)| format!("{}@{}", p, v))
                .join(" && "),
            self.orig.to_string()
        )
    }
}

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
        .search(egraph)
        .iter()
        .flat_map(|s| s.substs.iter().map(|s| *s.get(x).unwrap()))
        .collect();
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
