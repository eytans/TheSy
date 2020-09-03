use egg::{Applier, SymbolLang, EGraph, Var, Subst, Id, SearchMatches};

pub struct DiffApplier<T: Applier<SymbolLang, ()>> {
    applier: T
}

impl<T: Applier<SymbolLang, ()>> DiffApplier<T> {
    pub fn new(applier: T) -> DiffApplier<T> {
        DiffApplier { applier }
    }
}

impl<T: Applier<SymbolLang, ()>> Applier<SymbolLang, ()> for DiffApplier<T> {
    fn apply_matches(&self, egraph: &mut EGraph<SymbolLang, ()>, matches: &[SearchMatches]) -> Vec<Id> {
        let mut added = vec![];
        for mat in matches {
            for subst in &mat.substs {
                let ids = self.apply_one(egraph, mat.eclass, subst);
                //     .into_iter()
                //     .filter_map(|id| {
                //         let (to, did_something) = egraph.union(id, mat.eclass);
                //         if did_something {
                //             Some(to)
                //         } else {
                //             None
                //         }
                //     });
                // added.extend(ids)
            }
        }
        added
    }

    fn apply_one(&self, egraph: &mut EGraph<SymbolLang, ()>, eclass: Id, subst: &Subst) -> Vec<Id> {
        self.applier.apply_one(egraph, eclass, subst)
    }
}