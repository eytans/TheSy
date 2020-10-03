pub mod multisearcher {
    use std::collections::{HashMap, HashSet};
    use std::iter::FromIterator;
    use std::str::FromStr;

    use egg::{EGraph, Id, Pattern, Searcher, SearchMatches, Subst, SymbolLang, Var};
    use itertools::Itertools;

    use crate::tools::tools::Grouped;

    fn get_common_vars(patterns: &mut Vec<Pattern<SymbolLang>>) -> HashMap<Var, usize> {
        let common_vars = patterns.iter().flat_map(|p| p.vars())
            .grouped(|v| v.clone()).iter()
            .filter_map(|(k, v)|
                if v.len() <= 1 {None}
                else {Some((*k, v.len()))})
            .collect::<HashMap<Var, usize>>();

        fn count_commons(p: &Pattern<SymbolLang>, common_vars: &HashMap<Var, usize>) -> usize {
            p.vars().iter().map(|v| common_vars.get(v).unwrap_or(&0)).sum()
        }

        patterns.sort_by_key(|p| count_commons(&p, &common_vars));
        common_vars
    }

    fn merge_substs(vars: &Vec<Var>, sub1: &Subst, sub2: &Subst) -> Subst {
        let mut res = Subst::with_capacity(vars.len());
        for v in vars {
            let v1 = v.clone();
            let s1 = sub1.get(v1);
            let s2 = sub2.get(v1);
            if s1.is_some() || s2.is_some() {
                if s1.is_some() && s2.is_some() {
                    assert_eq!(s1.as_ref(), s2.as_ref());
                }
                res.insert(v1, s1.unwrap_or_else(|| s2.unwrap()).clone());
            }
        }
        res
    }

    // Aggregate product of equal common var substs
    fn aggregate_substs(possibilities: &[HashMap<Vec<Option<Id>>, Vec<Subst>>],
                        limits: Vec<&Option<Id>>,
                        all_vars: &Vec<Var>) -> Vec<Subst> {
        let current = possibilities.first().unwrap();
        // TODO: if matches can be taken directly from limitations then do so
        let matches = current.iter()
            .filter(|(keys, _)| limits.iter().zip(keys.iter())
                .all(|(lim, key)| lim.as_ref().map_or(true, |l| key.as_ref().map_or(true, |k| k == l))));
        if possibilities.len() > 1 {
            let mut collected = Vec::new();
            for (key, val) in matches {
                let new_limit: Vec<&Option<Id>> = limits.iter().zip(key)
                    .map(|(l, k)| if l.is_some() { l } else { k })
                    .collect();

                let rec_res = aggregate_substs(&possibilities[1..],
                                               new_limit,
                                               all_vars);
                collected.extend(rec_res.iter().cartesian_product(val)
                    .map(|(s1, s2)| merge_substs(all_vars, s1, s2)));
            }
            collected
        } else {
            matches.flat_map(|(_, v)| v.iter().map(|s| merge_substs(all_vars, s, s))).collect()
        }
    }

    fn group_by_common_vars(mut search_results: Vec<&mut SearchMatches>, common_vars: &HashMap<Var, usize>)
      -> Vec<HashMap<Vec<Option<Id>>, Vec<Subst>>> {
        let mut by_vars: Vec<HashMap<Vec<Option<Id>>, Vec<Subst>>> = Vec::new();
        for matches in search_results.iter_mut() {
            let cur_map: HashMap<Vec<Option<Id>>, Vec<Subst>> = {
                let substs: Vec<Subst> = std::mem::replace(&mut matches.substs, Vec::new());
                let grouped = substs.into_iter().grouped(|s| common_vars.keys()
                    .map(|v| s.get(v.clone()).map(|i| i.clone()))
                    .collect::<Vec<Option<Id>>>());
                grouped
            };
            by_vars.push(cur_map);
        }
        by_vars
    }

    #[derive(Clone)]
    pub struct MultiEqSearcher {
        patterns: Vec<Pattern<SymbolLang>>,
        common_vars: HashMap<Var, usize>,
    }

    impl MultiEqSearcher {
        pub(crate) fn new(mut patterns: Vec<Pattern<SymbolLang>>) -> MultiEqSearcher {
            let common_vars = get_common_vars(&mut patterns);
            MultiEqSearcher { patterns, common_vars }
        }

        pub fn pretty(&self, width: usize) -> String {
            self.patterns.iter().map(|p| p.pretty(width)).intersperse(" ||| ".to_string()).collect()
        }
    }

    impl Searcher<SymbolLang, ()> for MultiEqSearcher {
        fn search_eclass(&self, _: &EGraph<SymbolLang, ()>, _: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<SymbolLang, ()>) -> Vec<SearchMatches> {
            if self.patterns.len() == 1 {
                return self.patterns[0].search(egraph);
            }

            let mut search_results = {
                let mut res = Vec::new();
                for p in self.patterns.iter() {
                    let mut current = HashMap::new();
                    let searched = p.search(egraph);
                    for s in searched {
                        assert!(!current.contains_key(&s.eclass));
                        current.insert(s.eclass, s);
                    }
                    res.push(current);
                }
                res
            };

            let mut ids = search_results[0].keys().cloned().collect::<HashSet<Id>>();
            for r in search_results.iter().skip(1) {
                ids = ids.into_iter().filter(|k| r.contains_key(k)).collect();
            }

            ids.iter().filter_map(|k| {
                let eclass = *k;
                let mut inner_results = search_results.iter_mut().map(|m| m.remove(k).unwrap()).collect::<Vec<SearchMatches>>();
                // Take all search results and foreach pattern find the common variables and split by them.
                let by_vars = group_by_common_vars(
                    inner_results.iter_mut().collect(),
                    &self.common_vars);

                let initial_limits = (0..self.common_vars.len()).map(|_| &None).collect();
                let res = aggregate_substs(&by_vars[..], initial_limits, &self.vars());
                if res.is_empty() {None}
                else {Some(SearchMatches { substs: res, eclass })}
            }).collect()
        }

        fn vars(&self) -> Vec<Var> {
            Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()))
        }
    }

    impl FromStr for MultiEqSearcher {
        type Err = String;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            let patterns = s.split("|||")
                .map(|p| Pattern::from_str(p).unwrap())
                .collect::<Vec<Pattern<SymbolLang>>>();
            if patterns.len() == 1 {
                Err(String::from("Need at least two patterns"))
            } else {
                Ok(MultiEqSearcher::new(patterns))
            }
        }
    }

    #[derive(Clone)]
    pub struct MultiDiffSearcher {
        patterns: Vec<Pattern<SymbolLang>>,
        common_vars: HashMap<Var, usize>,
    }

    impl MultiDiffSearcher {
        pub fn new(mut patterns: Vec<Pattern<SymbolLang>>) -> MultiDiffSearcher {
            let common_vars = get_common_vars(&mut patterns);
            MultiDiffSearcher { patterns, common_vars }
        }

        pub fn pretty(&self, width: usize) -> String {
            self.patterns.iter().map(|p| p.pretty(width)).intersperse(" |||| ".to_string()).collect()
        }
    }

    impl Searcher<SymbolLang, ()> for MultiDiffSearcher {
        fn search_eclass(&self, _: &EGraph<SymbolLang, ()>, _: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<SymbolLang, ()>) -> Vec<SearchMatches> {
            if self.patterns.len() == 1 {
                return self.patterns[0].search(egraph);
            }

            let graph_string = format!("{:#?}", egraph);

            let mut search_results = {
                let mut res = Vec::new();
                for p in self.patterns.iter() {
                    let mut current = HashMap::new();
                    let searched = p.search(egraph);
                    for s in searched {
                        assert!(!current.contains_key(&s.eclass));
                        current.insert(s.eclass, s);
                    }
                    res.push(current);
                }
                res
            };

            // To reuse group_by_common_vars we will merge all results to a single searchmatches.
            // We don't really care which eclass we use so we will choose the first one.
            // It is a really stupid way to do it but we will run the grouping for each eclass from
            // the first one.

            let mut it = search_results.into_iter();
            let mut first = it.next();
            // I want to merge all subst except from first
            let mut all_matches = it.map(|mut m| m.into_iter()
                .map(|x| x.1)
                    .fold1(|mut s1, mut s2| {
                        s1.substs.extend(s2.substs.into_iter());
                        s1
                    }).unwrap_or(SearchMatches{substs: Vec::new(), eclass: Id::default()}))
                    .collect::<Vec<SearchMatches>>();
            if all_matches.iter().any(|s| s.substs.is_empty()) {
                return Vec::new();
            }

            let mut all_combinations = group_by_common_vars(
                all_matches.iter_mut().collect(),
                &self.common_vars);
            first.unwrap().into_iter().filter_map(|(k, mut matches)| {
                let eclass = k;
                let first_grouped = group_by_common_vars(vec![&mut matches], &self.common_vars).pop().unwrap();
                all_combinations.push(first_grouped);
                let initial_limits = (0..self.common_vars.len()).map(|_| &None).collect();
                let res = aggregate_substs(&all_combinations[..], initial_limits, &self.vars());
                all_combinations.pop();
                if res.is_empty() {None}
                else {
                    Some(SearchMatches { substs: res, eclass })
                }
            }).collect()
        }

        fn vars(&self) -> Vec<Var> {
            Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()))
        }
    }

    impl FromStr for MultiDiffSearcher {
        type Err = String;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            let patterns = s.split("||||")
                .map(|p| Pattern::from_str(p).unwrap())
                .collect::<Vec<Pattern<SymbolLang>>>();
            if patterns.len() == 1 {
                Err(String::from("Need at least two patterns"))
            } else {
                Ok(MultiDiffSearcher::new(patterns))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use egg::{EGraph, RecExpr, Searcher, SymbolLang};

    use crate::eggstentions::multisearcher::multisearcher::{MultiDiffSearcher, MultiEqSearcher};

    #[test]
    fn eq_two_trees_one_common() {
        let searcher: MultiEqSearcher = MultiEqSearcher::from_str("(a ?b ?c) ||| (a ?c ?d)").unwrap();
        let mut egraph: EGraph<SymbolLang, ()> = egg::EGraph::default();
        let x = egraph.add_expr(&RecExpr::from_str("x").unwrap());
        let z = egraph.add_expr(&RecExpr::from_str("z").unwrap());
        let a = egraph.add_expr(&RecExpr::from_str("(a x y)").unwrap());
        egraph.add_expr(&RecExpr::from_str("(a z x)").unwrap());
        egraph.rebuild();
        println!("{:#?}", searcher.search(&egraph));
        assert_eq!(searcher.search(&egraph).len(), 0);
        let a2 = egraph.add(SymbolLang::new("a", vec![z, x]));
        egraph.union(a, a2);
        egraph.rebuild();
        assert_eq!(searcher.search(&egraph).len(), 1);
    }

    #[test]
    fn diff_two_trees_one_common() {
        let searcher: MultiDiffSearcher = MultiDiffSearcher::from_str("(a ?b ?c) |||| (a ?c ?d)").unwrap();
        let mut egraph: EGraph<SymbolLang, ()> = egg::EGraph::default();
        let x = egraph.add_expr(&RecExpr::from_str("x").unwrap());
        let z = egraph.add_expr(&RecExpr::from_str("z").unwrap());
        let a = egraph.add_expr(&RecExpr::from_str("(a x y)").unwrap());
        egraph.add_expr(&RecExpr::from_str("(a z x)").unwrap());
        egraph.rebuild();
        println!("{:#?}", searcher.search(&egraph));
        assert_eq!(searcher.search(&egraph).len(), 1);
    }

    #[test]
    fn find_ind_hyp() {
        let mut egraph: EGraph<SymbolLang, ()> = EGraph::default();
        let full_pl = egraph.add_expr(&"(pl (S p0) Z)".parse().unwrap());
        let after_pl = egraph.add_expr(&"(S (pl p0 Z))".parse().unwrap());
        let sp0 = egraph.add_expr(&"(S p0)".parse().unwrap());
        let ind_var = egraph.add_expr(&"ind_var".parse().unwrap());
        egraph.union(ind_var, sp0);
        let ltwf = egraph.add_expr(&"(ltwf p0 (S p0))".parse().unwrap());
        egraph.union(full_pl, after_pl);
        egraph.rebuild();
        let searcher = MultiDiffSearcher::from_str("(ltwf ?x ind_var) |||| (pl ?x Z)").unwrap();
        assert!(!searcher.search(&egraph).is_empty());
    }
}