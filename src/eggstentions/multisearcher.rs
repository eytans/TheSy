mod multisearcher {
    use egg::{Pattern, Searcher, SymbolLang, EGraph, Var, Id, SearchMatches, Subst};
    use std::iter::FromIterator;
    use std::collections::{HashSet, HashMap};
    use crate::tools::tools::{combinations, print_iter};
    use itertools::Itertools;
    use std::iter;
    use std::str::FromStr;

    pub struct MultiSearcher {
        patterns: Vec<Pattern<SymbolLang>>,
        common_vars: HashMap<Var, usize>,
    }

    impl MultiSearcher {
        fn new(mut patterns: Vec<Pattern<SymbolLang>>) -> MultiSearcher {
            let mut common_vars = HashMap::new();
            for p in &patterns {
                for v in p.vars() {
                    if !common_vars.contains_key(&v) {
                        common_vars.insert(v.clone(), 0);
                    }
                    *common_vars.get_mut(&v).unwrap() += 1;
                }
            }
            let remove_keys = common_vars.keys().filter(|v| common_vars[v] <= 1);
            for k in Vec::from_iter(remove_keys.cloned()) {
                common_vars.remove(&k);
            }

            fn count_commons(p: &Pattern<SymbolLang>, common_vars: &HashMap<Var, usize>) -> usize {
                p.vars().iter().map(|v| common_vars.get(v).unwrap_or(&0)).sum()
            }

            patterns.sort_by_key(|p| count_commons(&p, &common_vars));
            println!("{:#?}", &common_vars);
            MultiSearcher { patterns, common_vars }
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
    }

    impl Searcher<SymbolLang, ()> for MultiSearcher {
        fn search_eclass(&self, egraph: &EGraph<SymbolLang, ()>, eclass: Id) -> Option<SearchMatches> {
            let search_results = self.patterns.iter()
                .map(|p| p.search_eclass(egraph, eclass)).collect::<Vec<Option<SearchMatches>>>();
            if search_results.iter().any(|i| i.is_none()) {
                return None;
            }

            // Take all search results and foreach pattern find the common variables and split by them.
            let mut by_vars: Vec<HashMap<Vec<Option<Id>>, Vec<&Subst>>> = Vec::new();
            for (i, matches) in search_results.iter()
                .map(|o| o.as_ref().unwrap())
                .enumerate() {
                let mut cur_map = HashMap::new();
                for s in &matches.substs {
                    let key = self.common_vars.keys().map(|v| s.get(v.clone()).map(|i| i.clone())).collect::<Vec<Option<Id>>>();
                    if !cur_map.contains_key(&key) {
                        cur_map.insert(key.clone(), Vec::new());
                    }
                    cur_map.get_mut(&key).unwrap().push(s);
                }
                by_vars.push(cur_map);
            }

            println!("{:#?}", by_vars);

            // Aggregate product of equal common var substs
            fn aggregate(possibilities: &[HashMap<Vec<Option<Id>>, Vec<&Subst>>], limits: Vec<&Option<Id>>, all_vars: &Vec<Var>) -> Vec<Subst> {
                let current = possibilities.first().unwrap();
                // TODO: if matches can be taken directly from limitations then do so
                let matches = current.iter()
                    .filter(|(keys, v)| limits.iter().zip(keys.iter())
                        .all(|(lim, key)| lim.as_ref().map_or(true, |l| key.as_ref().map_or(true, |k| k == l))))
                    .collect::<Vec<(&Vec<Option<Id>>, &Vec<&Subst>)>>();
                let mut collected = Vec::new();
                if possibilities.len() > 1 {
                    for (key, val) in matches {
                        let new_limit: Vec<&Option<Id>> = limits.iter().zip(key)
                            .map(|(l, k)| if l.is_some() { l } else { k })
                            .collect();
                        print_iter(new_limit.iter().map(|x| x.is_some()));
                        let rec_res = aggregate(&possibilities[1..],
                                                new_limit,
                                                all_vars);
                        collected.extend(rec_res.iter().cartesian_product(val)
                            .map(|(s1, s2)| MultiSearcher::merge_substs(all_vars, s1, s2)));
                    }
                } else {
                    for (k, v) in matches {
                        v.iter().for_each(|s| {
                            collected.push(s.clone().clone());
                        })
                    }
                }
                collected
            }

            let initial_limits = (0..self.common_vars.len()).map(|x| &None).collect();
            let res = aggregate(&by_vars[..], initial_limits, &self.vars());
            if res.is_empty() {None}
            else {Some(SearchMatches { substs: res, eclass })}
        }

        fn vars(&self) -> Vec<Var> {
            Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()))
        }
    }

    impl FromStr for MultiSearcher {
        type Err = String;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            let patterns = s.split("|||")
                .map(|p| Pattern::from_str(p).unwrap())
                .collect::<Vec<Pattern<SymbolLang>>>();
            if patterns.len() == 1 {
                Err(String::from("Need at least two patterns"))
            } else {
                Ok(MultiSearcher::new(patterns))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use egg::{RecExpr, EGraph, SymbolLang, Searcher};
    use std::str::FromStr;
    use crate::eggstentions::multisearcher::multisearcher::MultiSearcher;

    #[test]
    fn two_trees_one_common() {
        let searcher: MultiSearcher = MultiSearcher::from_str("(a ?b ?c) ||| (a ?c ?d)").unwrap();
        let mut egraph: EGraph<SymbolLang, ()> = egg::EGraph::default();
        let x = egraph.add_expr(&RecExpr::from_str("x").unwrap());
        let z = egraph.add_expr(&RecExpr::from_str("z").unwrap());
        let a = egraph.add_expr(&RecExpr::from_str("(a x y)").unwrap());
        egraph.add_expr(&RecExpr::from_str("(a z x)").unwrap());
        println!("{:#?}", searcher.search(&egraph));
        assert_eq!(searcher.search(&egraph).len(), 0);
        let a2 = egraph.add(SymbolLang::new("a", vec![z, x]));
        egraph.union(a, a2);
        assert_eq!(searcher.search(&egraph).len(), 1);
    }
}