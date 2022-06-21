pub mod multisearcher {
    use std::iter::FromIterator;
    use std::str::FromStr;

    use egg::{EGraph, Id, Pattern, Searcher, SearchMatches, Subst, SymbolLang, Var, Language, Analysis, Condition, ImmutableCondition, RcImmutableCondition, ENodeOrVar};
    use itertools::{Itertools, Either};

    use crate::tools::tools::Grouped;
    use crate::eggstentions::pretty_string::PrettyString;
    use std::fmt::Debug;
    use smallvec::alloc::fmt::Formatter;
    use std::marker::PhantomData;
    use std::rc::Rc;
    use indexmap::{IndexMap, IndexSet};
    use thesy_parser::ast::Expression;
    use crate::eggstentions::expression_ops::{IntoTree, RecExpSlice, Tree};
    use crate::tools::tools;

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

    impl<L: Language, N: Analysis<L>, A: Searcher<L, N> + Debug, B: Searcher<L, N> + Debug> std::fmt::Display for EitherSearcher<L, N, A, B> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            match &self.node {
                Either::Left(x) => { write!(f, "{}", x) }
                Either::Right(x) => { write!(f, "{}", x) }
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

    fn get_common_vars(patterns: &mut Vec<impl Searcher<SymbolLang, ()>>) -> IndexMap<Var, usize> {
        let common_vars = patterns.iter().flat_map(|p| p.vars())
            .grouped(|v| v.clone()).iter()
            .filter_map(|(k, v)|
                if v.len() <= 1 { None } else { Some((*k, v.len())) })
            .collect::<IndexMap<Var, usize>>();

        fn count_commons(p: &impl Searcher<SymbolLang, ()>, common_vars: &IndexMap<Var, usize>) -> usize {
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
    fn aggregate_substs(possibilities: &[IndexMap<Vec<Option<Id>>, Vec<Subst>>],
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

    fn group_by_common_vars(mut search_results: Vec<&mut SearchMatches>, common_vars: &IndexMap<Var, usize>)
                            -> Vec<IndexMap<Vec<Option<Id>>, Vec<Subst>>> {
        let mut by_vars: Vec<IndexMap<Vec<Option<Id>>, Vec<Subst>>> = Vec::new();
        for matches in search_results.iter_mut() {
            let cur_map: IndexMap<Vec<Option<Id>>, Vec<Subst>> = {
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
        common_vars: IndexMap<Var, usize>,
    }

    impl<A: Searcher<SymbolLang, ()>> std::fmt::Display for MultiEqSearcher<A> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.patterns.iter().map(|x| x.to_string()).join(" =:= "))
        }
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
                    let mut current = IndexMap::new();
                    let searched = p.search(egraph);
                    for s in searched {
                        assert!(!current.contains_key(&s.eclass));
                        current.insert(s.eclass, s);
                    }
                    res.push(current);
                }
                res
            };

            let mut ids = search_results[0].keys().cloned().collect::<IndexSet<Id>>();
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
        common_vars: IndexMap<Var, usize>,
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

    impl<S: Searcher<SymbolLang, ()> + 'static> std::fmt::Display for MultiDiffSearcher<S> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.patterns.iter().map(|x| x.to_string()).join(" ||| "))
        }
    }

    // impl PrettyString for MultiDiffSearcher {
    //     fn pretty_string(&self) -> String {
    //         self.patterns.iter().map(|p| p.pretty_string()).intersperse(" |||| ".to_string()).collect()
    //     }
    // }

    impl<A: 'static + Searcher<SymbolLang, ()>> Searcher<SymbolLang, ()> for MultiDiffSearcher<A> {
        fn search_eclass(&self, _: &EGraph<SymbolLang, ()>, _: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<SymbolLang, ()>) -> Vec<SearchMatches> {
            if self.patterns.len() == 1 {
                return self.patterns[0].search(egraph);
            }

            // TODO: we dont need a IndexMap here
            let mut search_results = {
                let mut res = Vec::new();
                for p in self.patterns.iter() {
                    let mut current = IndexMap::new();
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

    impl<L: Language, N: Analysis<L>> ImmutableCondition<L, N> for SubPattern<L> {
        fn check_imm(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool {
            let mut res = true;
            for (var, pattern) in &self.patterns {
                // Get eclass from the substitution
                let eclass = subst.get(var.clone()).unwrap_or_else(|| {
                    panic!("{} not found in {}", var, subst)
                });
                let subs = pattern.search_eclass(egraph, *eclass);
                res &= subs.is_some();
                if pattern.vars().iter().any(|v| subst.get(*v).is_some()) {
                    res &= subs.unwrap().substs.iter().any(|s| {
                        pattern.vars().iter()
                            .filter(|v| subst.get(**v).is_some())
                            .all(|v| s.get(*v) == subst.get(*v))
                    })
                }
            }
            res
        }

        fn describe(&self) -> String {
            format!("{} if {}", self.orig.to_string(), self.patterns.iter().map(|(v, p)| format!("{}@{}", p, v)).join(" && "))
        }
    }

    #[derive(Clone)]
    pub struct FilteringSearcher<L: Language, N: Analysis<L>> {
        searcher: Rc<dyn Searcher<L, N>>,
        predicate: RcImmutableCondition<L, N>,
        phantom_ln: PhantomData<(L, N)>,
    }

    impl<L: Language + 'static, N: Analysis<L> + 'static> FilteringSearcher<L, N> {
        pub fn matcher_from_var(var: Var) -> Rc<dyn Fn(&EGraph<L, N>, &Subst) -> Option<Id>> {
            Rc::new(move |graph, sbt|
                sbt.get(var).copied())
        }

        pub fn matcher_from_enode(enode: L) -> Rc<dyn Fn(&EGraph<L, N>, &Subst) -> Option<Id>> {
            Rc::new(move |graph, sbt| graph.lookup(enode.clone()))
        }

        pub fn matcher_from_pattern(p: Pattern<L>)
            -> Rc<dyn Fn(&EGraph<L, N>, &Subst) -> Option<Id>> {
            // The parser asserts all vars are present.
            Rc::new(move |graph, sbt| p.rec_lookup(graph, sbt))
        }

        pub fn create_non_pattern_filterer(matcher: Rc<dyn Fn(&EGraph<L, N>, &Subst) -> Option<Id>>,
                                           negator: Rc<dyn Fn(&EGraph<L, N>, &Subst) -> Option<Id>>)
            -> RcImmutableCondition<L, N> {
            let x = (move |graph: &EGraph<L, N>, id: Id, subst: &Subst| {
                let m = matcher(graph, subst);
                m.is_none() || m != negator(graph, subst)
            });
            RcImmutableCondition::new(x)
        }

        pub fn create_exists_pattern_filterer(searcher: Pattern<L>) -> RcImmutableCondition<L, N> {
            // TODO: partially fill pattern and if not all vars have values then search by eclass
            //       In practice, create special searcher that will take the constant part from
            //       subst and check existence for each subpattern over eclasses found in subst
            RcImmutableCondition::new(move |graph: &EGraph<L, N>, eclass: Id, subst: &Subst| {
                searcher.rec_lookup(graph, subst).is_some()
            })
        }

        pub fn new(searcher: Rc<dyn Searcher<L, N>>,
                   predicate: RcImmutableCondition<L, N>, ) -> Self {
            FilteringSearcher {
                searcher,
                predicate,
                phantom_ln: Default::default()
            }
        }

        pub fn from<S: Searcher<L, N> + 'static>(s: S, predicate: RcImmutableCondition<L, N>) -> Self {
            let dyn_searcher: Rc<dyn Searcher<L, N>> = Rc::new(s);
            Self::new(dyn_searcher, predicate)
        }
    }

    impl<L: Language + 'static, N: Analysis<L> + 'static> std::fmt::Display for FilteringSearcher<L, N> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{} if {}", self.searcher, self.predicate.describe())
        }
    }

    impl<L: 'static + Language, N: 'static + Analysis<L>> Searcher<L, N> for FilteringSearcher<L, N> {
        fn search_eclass(&self, egraph: &EGraph<L, N>, eclass: Id) -> Option<SearchMatches> {
            unimplemented!()
        }

        fn search(&self, egraph: &EGraph<L, N>) -> Vec<SearchMatches> {
            warn!("Running {} with {}", self.searcher, self.predicate.describe());
            let origin = self.searcher.search(egraph);
            let res = self.predicate.filter(egraph, origin);
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
        searcher: Rc<dyn Searcher<L, N>>,
    }

    impl<L: Language, N: Analysis<L>> PointerSearcher<L, N> {
        pub fn new(searcher: Rc<dyn Searcher<L, N>>) -> Self { PointerSearcher { searcher } }
    }

    impl<L: Language, N: Analysis<L>> std::fmt::Display for PointerSearcher<L, N> {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.searcher)
        }
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

    use egg::{EGraph, RecExpr, Searcher, SymbolLang, Pattern};

    use crate::eggstentions::searchers::multisearcher::{MultiDiffSearcher, MultiEqSearcher, FilteringSearcher};

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

    #[test]
    fn pattern_to_matcher_sanity() {
        let mut graph: EGraph<SymbolLang, ()> = EGraph::default();
        graph.add_expr(&RecExpr::from_str("(+ 1 (+ 2 3))").unwrap());
        graph.add_expr(&RecExpr::from_str("(+ 31 (+ 32 33))").unwrap());
        graph.add_expr(&RecExpr::from_str("(+ 21 (+ 22 23))").unwrap());
        graph.add_expr(&RecExpr::from_str("(+ 11 (+ 12 13))").unwrap());
        let p: Pattern<SymbolLang> = Pattern::from_str("(+ ?z (+ ?x ?y))").unwrap();
        let m = FilteringSearcher::matcher_from_pattern(p.clone());
        let results = p.search(&graph);
        for sm in results {
            let eclass = sm.eclass;
            for sb in sm.substs {
                assert_eq!(Some(eclass), m(&graph, &sb));
            }
        }
    }
}