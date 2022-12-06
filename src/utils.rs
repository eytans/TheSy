use std::iter::FromIterator;
use std::str::FromStr;
use egg::{Analysis, ColorId, EGraph, ENodeOrVar, Id, ImmutableCondition, IntoTree, Language, Pattern, Searcher, Subst, ToCondRc, Tree, Var};
use itertools::Itertools;
use thesy_parser::ast::Expression;
use egg::expression_ops::RecExpSlice;
use egg::pretty_string::PrettyString;
use indexmap::IndexSet;

/**
* [orig] is the expression of the `Subst` in [check_imm].
*/
#[derive(Clone, Debug)]
pub struct SubPattern<L: Language> {
    orig: Expression,
    pub patterns: Vec<(Var, Pattern<L>)>,
}

impl<L: Language> SubPattern<L> {
    fn collect_patterns(orig: &Expression, pattern_tree: &RecExpSlice<ENodeOrVar<L>>) -> Result<Vec<(Var, Pattern<L>)>, String> {
        let mut res = Vec::new();
        // For each node in the orig pattern we will check the new pattern.
        //  1. If orig and new pattern are nodes assert they agree, otherwise error.
        if orig.root().is_id() && pattern_tree.is_root_ident() {
            if orig.children().len() != pattern_tree.children().len() ||
                orig.root().ident() != &pattern_tree.root().display_op().to_string() {
                return Err(format!("Patterns don't agree: {}{} != {}{}",
                                   orig.root().ident(), orig.children().len(),
                                   pattern_tree.root().display_op(), pattern_tree.children().len()));
            }
            for (orig_child, pattern_child) in orig.children().iter().zip(pattern_tree.children().iter()) {
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
            if orig.root().to_string() == pattern_tree.root().display_op().to_string().replace("?", "") {
                return Err(format!("Patterns don't agree: {} != {}",
                                   orig.root().ident(), pattern_tree.root().display_op()));
            }
        }
        Ok(res)
    }

    pub fn new(orig: Expression, pattern: Pattern<L>) -> Self {
        let pattern_tree = pattern.ast.into_tree();
        debug_assert_eq!(orig.root().ident(), &pattern_tree.root().display_op().to_string());
        let patterns = Self::collect_patterns(&orig, &pattern_tree);
        patterns.map(|p| SubPattern { orig, patterns: p }).unwrap_or_else(|e| {
            panic!("{}", e)
        })
    }
}

impl<L: Language, N: Analysis<L>> ToCondRc<L, N> for SubPattern<L> {}

impl<L: Language, N: Analysis<L>> ImmutableCondition<L, N> for SubPattern<L> {
    fn check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
        let colores = self.colored_check_imm(egraph, eclass, subst);
        return if colores.is_none() {
            false
        } else if colores.as_ref().unwrap().is_empty() {
            true
        } else {
            subst.color().is_some() && colores.unwrap().contains(&subst.color().unwrap())
        };
    }

    fn colored_check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> Option<Vec<ColorId>> {
        // Same as check_imm but collects colors to use when comparing vars for each pattern.
        // If no patterns in self then it is true always (i.e. returns black).
        let mut res = vec![];
        'patterns: for (var, pattern) in &self.patterns {
            // Get eclass from the substitution
            let eclass = subst.get(var.clone()).unwrap_or_else(|| {
                panic!("{} not found in {}", var, subst)
            });
            let subs = if let Some(c) = subst.color() {
                pattern.colored_search_eclass(egraph, *eclass, c)
            } else {
                pattern.search_eclass(egraph, *eclass)
            };
            if subs.is_none() {
                return None;
            }

            // Check if pattern vars matter
            let vars = pattern.vars().iter().copied()
                .filter(|v| subst.get(*v).is_some()).collect_vec();
            if vars.is_empty() {
                continue 'patterns;
            }

            // If black continue outer loop.
            // If it is not black, collect/update possible colors in res using what is found in
            // pattern_colors.
            let mut pattern_colors: IndexSet<ColorId> = Default::default();
            for s in subs.unwrap().substs {
                let mut not_equal_vars = vars.iter().filter(|v| {
                    let v = **v;
                    debug_assert_eq!(egraph.opt_colored_find(s.color(), *s.get(v).unwrap()), *s.get(v).unwrap());
                    debug_assert_eq!(egraph.opt_colored_find(subst.color(), *subst.get(v).unwrap()), *subst.get(v).unwrap());
                    s.get(v) != subst.get(v)
                }).copied().collect_vec();
                if not_equal_vars.is_empty() {
                    continue 'patterns;
                }
                // In the future if we support #hierarcal_colors we should not return here.
                if s.color().is_some() {
                    return None;
                }

                let colored_equalities_for_var = |v: Var| {
                    egraph.get_colored_equalities(*s.get(v).unwrap())
                        .map(|x| x.iter()
                        .filter(|(c_id, id)|
                            *id == egraph.opt_colored_find(Some(*c_id), *subst.get(v).unwrap()))
                        .map(|(c_id, _)| c_id).copied().collect_vec()).unwrap_or_default()
                };
                // We need to recalculate all agree, but consider colored equalities.
                let mut working_colors: IndexSet<ColorId> = IndexSet::from_iter({
                    colored_equalities_for_var(not_equal_vars.pop().unwrap()).into_iter()
                });
                if working_colors.is_empty() {
                    return None;
                }
                for v in not_equal_vars {
                    let colors: IndexSet<ColorId> = IndexSet::from_iter({
                        colored_equalities_for_var(v).into_iter()
                    });
                    working_colors = working_colors.intersection(&colors).copied().collect();
                    if working_colors.is_empty() {
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
                    return None;
                }
            }
        }
        Some(res)
    }

    fn describe(&self) -> String {
        format!("{} -> {}", self.patterns.iter().map(|(v, p)| format!("{}@{}", p, v)).join(" && "), self.orig.to_string())
    }
}
