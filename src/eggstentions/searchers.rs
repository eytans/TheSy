pub mod multisearcher {
    use std::collections::{HashMap, HashSet};
    use std::iter::FromIterator;
    use std::str::FromStr;

    use egg::{EGraph, Id, Pattern, Searcher, SearchMatches, Subst, SymbolLang, Var, Language, Analysis};
    use itertools::{Itertools, Either};

    use crate::tools::tools::Grouped;
    use crate::eggstentions::pretty_string::PrettyString;
    use std::fmt::Debug;
    use smallvec::alloc::fmt::Formatter;
    use std::marker::PhantomData;
    use std::rc::Rc;

    pub struct EitherSearcher<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug, B: Searcher<L, N> + Debug> {
        node: Either<A, B>,
        phantom: PhantomData<(L, N)>,
    }

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug, B: Searcher<L, N> + Debug> EitherSearcher<L, N, A, B> {
        pub fn left(a: A) -> EitherSearcher<L, N, A, B> {
            EitherSearcher { node: Either::Left(a), phantom: PhantomData::default() }
        }

        pub fn right(b: B) -> EitherSearcher<L, N, A, B> {
            EitherSearcher { node: Either::Right(b), phantom: PhantomData::default() }
        }
    }

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug, B: Searcher<L, N> + Debug> Searcher<L, N> for EitherSearcher<L, N, A, B> {
        fn search_eclass(&self, egraph: &EGraph<L, N>, eclass: Id) -> Option<SearchMatches> {
            if self.node.is_left() {
                self.node.as_ref().left().unwrap().search_eclass(egraph, eclass)
            } else {
                self.node.as_ref().right().unwrap().search_eclass(egraph, eclass)
            }
        }

        fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
            if self.node.is_left() {
                self.node.as_ref().left().unwrap().search(egraph)
            } else {
                self.node.as_ref().right().unwrap().search(egraph)
            }
        }

        fn vars(&self) -> Vec<Var> {
            if self.node.is_left() {
                self.node.as_ref().left().unwrap().vars()
            } else {
                self.node.as_ref().right().unwrap().vars()
            }
        }
    }

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug + Clone, B: Searcher<L, N> + Debug + Clone> Clone for EitherSearcher<L, N, A, B> {
        fn clone(&self) -> Self {
            if self.node.is_left() {
                Self::left(self.node.as_ref().left().unwrap().clone())
            } else {
                Self::right(self.node.as_ref().right().unwrap().clone())
            }
        }
    }

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug + PrettyString, B: Searcher<L, N> + Debug + PrettyString> PrettyString for EitherSearcher<L, N, A, B> {
        fn pretty_string(&self) -> String {
            if self.node.is_left() {
                self.node.as_ref().left().unwrap().pretty_string()
            } else {
                self.node.as_ref().right().unwrap().pretty_string()
            }
        }
    }

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug, B: Searcher<L, N> + Debug> Debug for EitherSearcher<L, N, A, B> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            self.node.fmt(f)
        }
    }

    fn get_common_vars(patterns: &mut Vec<impl Searcher<SymbolLang, ()>>) -> HashMap<Var, usize> {
        let common_vars = patterns.iter().flat_map(|p| p.vars())
            .grouped(|v| v.clone()).iter()
            .filter_map(|(k, v)|
                if v.len() <= 1 { None } else { Some((*k, v.len())) })
            .collect::<HashMap<Var, usize>>();

        fn count_commons(p: &impl Searcher<SymbolLang, ()>, common_vars: &HashMap<Var, usize>) -> usize {
            p.vars().iter().map(|v| common_vars.get(v).unwrap_or(&0)).sum()
        }

        patterns.sort_by_key(|p| count_commons(p, &common_vars));
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

    pub struct MultiEqSearcher<A: Searcher<SymbolLang, ()>> {
        patterns: Vec<A>,
        common_vars: HashMap<Var, usize>,
    }

    impl<A: Searcher<SymbolLang, ()>> MultiEqSearcher<A> {
        pub(crate) fn new(mut patterns: Vec<A>) -> MultiEqSearcher<A> {
            let common_vars = get_common_vars(&mut patterns);
            MultiEqSearcher { patterns, common_vars }
        }
    }

    impl<A: Searcher<SymbolLang, ()> + PrettyString> PrettyString for MultiEqSearcher<A> {
        fn pretty_string(&self) -> String {
            self.patterns.iter().map(|p| p.pretty_string()).intersperse(" ||| ".to_string()).collect()
        }
    }

    impl<A: Searcher<SymbolLang, ()>> Searcher<SymbolLang, ()> for MultiEqSearcher<A> {
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
                if res.is_empty() { None } else { Some(SearchMatches { substs: res, eclass }) }
            }).collect()
        }

        fn vars(&self) -> Vec<Var> {
            Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()))
        }
    }

    impl FromStr for MultiEqSearcher<Pattern<SymbolLang>> {
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

    impl<A: Searcher<SymbolLang, ()> + Clone> Clone for MultiEqSearcher<A> {
        fn clone(&self) -> Self {
            MultiEqSearcher::new(self.patterns.clone())
        }
    }

    impl<A: Searcher<SymbolLang, ()> + Debug> Debug for MultiEqSearcher<A> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            f.debug_list().entries(&self.patterns).finish()
        }
    }

    pub struct MultiDiffSearcher<A: Searcher<SymbolLang, ()>> {
        patterns: Vec<A>,
        common_vars: HashMap<Var, usize>,
    }

    impl<A: Searcher<SymbolLang, ()>> MultiDiffSearcher<A> {
        pub fn new(mut patterns: Vec<A>) -> MultiDiffSearcher<A> {
            let common_vars = get_common_vars(&mut patterns);
            MultiDiffSearcher { patterns, common_vars }
        }
    }

    impl<S: Searcher<SymbolLang, ()> + 'static> ToDyn<SymbolLang, ()> for MultiDiffSearcher<S> {
        fn into_rc_dyn(self) -> Rc<dyn Searcher<SymbolLang, ()>> {
            let dyn_s: Rc<dyn Searcher<SymbolLang, ()>> = Rc::new(self);
            dyn_s
        }
    }

    impl<S: Searcher<SymbolLang, ()> + 'static> ToDyn<SymbolLang, ()> for MultiEqSearcher<S> {
        fn into_rc_dyn(self) -> Rc<dyn Searcher<SymbolLang, ()>> {
            let dyn_s: Rc<dyn Searcher<SymbolLang, ()>> = Rc::new(self);
            dyn_s
        }
    }

    // impl PrettyString for MultiDiffSearcher {
    //     fn pretty_string(&self) -> String {
    //         self.patterns.iter().map(|p| p.pretty_string()).intersperse(" |||| ".to_string()).collect()
    //     }
    // }

    impl<A: Searcher<SymbolLang, ()>> Searcher<SymbolLang, ()> for MultiDiffSearcher<A> {
        fn search_eclass(&self, _: &EGraph<SymbolLang, ()>, _: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<SymbolLang, ()>) -> Vec<SearchMatches> {
            if self.patterns.len() == 1 {
                return self.patterns[0].search(egraph);
            }

            // TODO: we dont need a hashmap here
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
                }).unwrap_or(SearchMatches { substs: Vec::new(), eclass: Id::default() }))
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
                if res.is_empty() { None } else {
                    Some(SearchMatches { substs: res, eclass })
                }
            }).collect()
        }

        fn vars(&self) -> Vec<Var> {
            Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()).sorted().dedup())
        }
    }

    impl FromStr for MultiDiffSearcher<Pattern<SymbolLang>> {
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

    impl<A: Searcher<SymbolLang, ()> + Clone> Clone for MultiDiffSearcher<A> {
        fn clone(&self) -> Self {
            MultiDiffSearcher::new(self.patterns.clone())
        }
    }

    impl<A: Searcher<SymbolLang, ()> + Debug> Debug for MultiDiffSearcher<A> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            f.debug_list().entries(&self.patterns).finish()
        }
    }

    impl<A: Searcher<SymbolLang, ()> + PrettyString> PrettyString for MultiDiffSearcher<A> {
        fn pretty_string(&self) -> String {
            self.patterns.iter().map(|p| p.pretty_string()).intersperse(" ||| ".to_string()).collect()
        }
    }

    pub type MatchFilter<L: Language, N: Analysis<L>> = Rc<dyn Fn(&EGraph<L, N>, Vec<SearchMatches>) -> Vec<SearchMatches>>;

    #[derive(Clone)]
    pub struct FilteringSearcher<L: Language, N: Analysis<L>> {
        searcher: Rc<dyn Searcher<L, N>>,
        predicate: Rc<dyn Fn(&EGraph<L, N>, Vec<SearchMatches>) -> Vec<SearchMatches>>,
        phantom_ln: PhantomData<(L, N)>,
    }

    impl<L: Language + 'static, N: Analysis<L> + 'static> FilteringSearcher<L, N> {
        pub fn create_non_pattern_filterer(searcher: Rc<dyn Searcher<L, N>>, root: Var) ->
        Rc<dyn Fn(&EGraph<L, N>, Vec<SearchMatches>) -> Vec<SearchMatches>> {
            Rc::new(move |graph: &EGraph<L, N>, sms: Vec<SearchMatches>| {
                let res = searcher.search(graph).iter().map(|s| s.eclass).collect::<HashSet<Id>>();
                sms.into_iter().filter_map(|mut sm | {
                    let mut substs = std::mem::take(&mut sm.substs);
                    sm.substs = substs.into_iter().filter(|s| !res.contains(&s[root])).collect_vec();
                    if sm.substs.is_empty() {
                        None
                    } else {
                        Some(sm)
                    }
                }).collect_vec()
            })
        }

        pub fn create_exists_pattern_filterer(searcher: Rc<dyn Searcher<L, N>>, root: Var) ->
        Rc<dyn Fn(&EGraph<L, N>, Vec<SearchMatches>) -> Vec<SearchMatches>> {
            Rc::new(move |graph: &EGraph<L, N>, sms: Vec<SearchMatches>| {
                let res = searcher.search(graph).iter().map(|s| s.eclass).collect::<HashSet<Id>>();
                sms.into_iter().filter_map(|mut sm| {
                    let mut substs = std::mem::take(&mut sm.substs);
                    sm.substs = substs.into_iter().filter(|s| res.contains(&s[root])).collect_vec();
                    if sm.substs.is_empty() {
                        None
                    } else {
                        Some(sm)
                    }
                }).collect_vec()
            })
        }

        pub fn new(searcher: Rc<dyn Searcher<L, N>>,
                   predicate: MatchFilter<L, N>, ) -> Self {
            FilteringSearcher { searcher, predicate, phantom_ln: Default::default() }
        }

        pub fn from<S: Searcher<L, N> + 'static>(s: S, predicate: MatchFilter<L, N>) -> Self {
            let dyn_searcher: Rc<dyn Searcher<L, N>> = Rc::new(s);
            Self::new(dyn_searcher, predicate)
        }
    }

    pub fn aggregate_conditions<L: Language + 'static, N: Analysis<L> + 'static>(conditions: Vec<MatchFilter<L, N>>) -> MatchFilter<L, N> {
        Rc::new(move |graph: &EGraph<L, N>, mut sms: Vec<SearchMatches>| {
            for c in &conditions {
                sms = c(graph, sms);
            }
            sms
        })
    }

    impl<L: Language, N: Analysis<L>> Searcher<L, N> for FilteringSearcher<L, N> {
        fn search_eclass(&self, egraph: &EGraph<L, N>, eclass: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
            let origin = self.searcher.search(egraph);
            let res = (self.predicate)(egraph, origin);
            res
        }

        fn vars(&self) -> Vec<Var> {
            self.searcher.vars()
        }
    }

    pub trait ToDyn<L: Language, N: Analysis<L>> {
        fn into_rc_dyn(self) -> Rc<dyn Searcher<L, N>>;
    }

    impl<L: Language + 'static, N: Analysis<L> + 'static> ToDyn<L, N> for Pattern<L> {
        fn into_rc_dyn(self) -> Rc<dyn Searcher<L, N>> {
            let dyn_s: Rc<dyn Searcher<L, N>> = Rc::new(self);
            dyn_s
        }
    }

    impl<L: Language + 'static, N: Analysis<L> + 'static> ToDyn<L, N> for FilteringSearcher<L, N> {
        fn into_rc_dyn(self) -> Rc<dyn Searcher<L, N>> {
            let dyn_s: Rc<dyn Searcher<L, N>> = Rc::new(self);
            dyn_s
        }
    }

    pub struct PointerSearcher<L: Language, N: Analysis<L>> {
        searcher: Rc<dyn Searcher<L, N>>
    }

    impl<L: Language, N: Analysis<L>> PointerSearcher<L, N> {
        pub fn new(searcher: Rc<dyn Searcher<L, N>>) -> Self { PointerSearcher{searcher} }
    }

    impl<L: Language, N: Analysis<L>> Searcher<L, N> for PointerSearcher<L, N> {
        fn search_eclass(&self, egraph: &EGraph<L, N>, eclass: Id) -> Option<SearchMatches> {
            self.searcher.search_eclass(egraph, eclass)
        }

        fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
            self.searcher.search(egraph)
        }

        fn vars(&self) -> Vec<Var> {
            self.searcher.vars()
        }
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use egg::{EGraph, RecExpr, Searcher, SymbolLang};

    use crate::eggstentions::searchers::multisearcher::{MultiDiffSearcher, MultiEqSearcher};

    #[test]
    fn eq_two_trees_one_common() {
        let searcher = MultiEqSearcher::from_str("(a ?b ?c) ||| (a ?c ?d)").unwrap();
        let mut egraph: EGraph<SymbolLang, ()> = egg::EGraph::default();
        let x = egraph.add_expr(&RecExpr::from_str("x").unwrap());
        let z = egraph.add_expr(&RecExpr::from_str("z").unwrap());
        let a = egraph.add_expr(&RecExpr::from_str("(a x y)").unwrap());
        egraph.add_expr(&RecExpr::from_str("(a z x)").unwrap());
        egraph.rebuild();
        assert_eq!(searcher.search(&egraph).len(), 0);
        let a2 = egraph.add(SymbolLang::new("a", vec![z, x]));
        egraph.union(a, a2);
        egraph.rebuild();
        assert_eq!(searcher.search(&egraph).len(), 1);
    }

    #[test]
    fn diff_two_trees_one_common() {
        let searcher = MultiDiffSearcher::from_str("(a ?b ?c) |||| (a ?c ?d)").unwrap();
        let mut egraph: EGraph<SymbolLang, ()> = egg::EGraph::default();
        let x = egraph.add_expr(&RecExpr::from_str("x").unwrap());
        let z = egraph.add_expr(&RecExpr::from_str("z").unwrap());
        let a = egraph.add_expr(&RecExpr::from_str("(a x y)").unwrap());
        egraph.add_expr(&RecExpr::from_str("(a z x)").unwrap());
        egraph.rebuild();
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