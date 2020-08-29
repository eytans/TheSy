use egg::{Pattern, Searcher, SymbolLang, EGraph, Var, Id, SearchMatches};
use std::iter::FromIterator;
use std::collections::{HashSet, HashMap};

struct MultiSearcher {
    patterns: Vec<Pattern<SymbolLang>>,
    common_vars: HashMap<Var, usize>
}

impl MultiSearcher {
    fn new(patterns: Vec<Pattern<SymbolLang>>) -> MultiSearcher {
        let mut common_vars = HashMap::new();
        for p in &patterns {
            for v in p.vars() {
                if !common_vars.contains_key(&v){
                    common_vars.insert(v.clone(), 0);
                }
                *common_vars.get_mut(&v).unwrap() += 1;
            }
        }
        let remove_keys = common_vars.keys().filter(|v| common_vars[v] > 1);
        for k in Vec::from_iter(remove_keys.cloned()) {
            common_vars.remove(&k);
        }
        MultiSearcher{patterns, common_vars}
    }
}

impl Searcher<SymbolLang, ()> for MultiSearcher {
    fn search_eclass(&self, egraph: &EGraph<SymbolLang, ()>, eclass: Id) -> Option<SearchMatches> {
        unimplemented!()
    }

    fn vars(&self) -> Vec<Var> {
        Vec::from_iter(self.patterns.iter().flat_map(|p| p.vars()))
    }
}