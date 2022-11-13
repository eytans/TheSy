use egg::{RecExpr, SymbolLang};
use itertools::Itertools;

use egg::expression_ops::{IntoTree};
use crate::lang::{DataType, Function, ThExpr};
use std::collections::hash_map::RandomState;
use indexmap::IndexMap;

#[derive(Clone, Debug)]
pub struct Examples {
    pub datatype: DataType,
    examples: Vec<ThExpr>,
    example_vars: Vec<IndexMap<Function, Vec<ThExpr>>>,
}

impl Examples {
    /// For now I will create full examples?
/// Will be very expensive for trees but will deal with that later
    pub fn examples(&self) -> &[ThExpr] {
        &self.examples
    }

    pub fn new(datatype: &DataType, max_depth: usize) -> Self {
        let mut constructor_phs: Vec<IndexMap<Function, Vec<ThExpr>, RandomState>> = Default::default();
        let mut ph_counts: IndexMap<ThExpr, usize> = IndexMap::new();
        let mut res = datatype.constructors.iter()
            .filter(|f| !f.params.contains(&datatype.as_exp()))
            .map(|f| f.apply_params(f.params.iter().map(|p| {
                let index = *ph_counts.entry(p.clone()).or_insert(0);
                *ph_counts.get_mut(p).unwrap() += 1;
                format!("autovar_{}_{}", p.into_tree().to_spaceless_string(), index).parse().unwrap()
            }).collect_vec())).collect_vec();
        let constructors = datatype.constructors.iter()
            .filter(|f| f.params.contains(&datatype.as_exp())).collect_vec();
        for _ in 0..max_depth {
            constructor_phs.push(IndexMap::new());
            let last_example = res.last().unwrap().clone();
            res.extend(constructors.iter().map(|constr| {
                // Creating example by creating ph and using as params.
                // Reusing old examples, doesn't matter how we build them so for now straight forward.
                constr.apply_params(constr.params.iter()
                    .map(|p| {
                        // Comparing trees is more safe
                        if p.into_tree() != datatype.as_exp().into_tree() {
                            let index = *ph_counts.entry(p.clone()).or_insert(0);
                            *ph_counts.get_mut(p).unwrap() += 1;
                            let new_ph: ThExpr = format!("autovar_{}_{}", p.into_tree().to_spaceless_string(), index).parse().unwrap();
                            constructor_phs.last_mut().unwrap().entry(constr.clone().clone()).or_insert(vec![]).push(new_ph.clone());
                            new_ph
                        } else {
                            last_example.clone()
                        }
                    }).collect_vec())
            }));
        }
        for ex in res.iter() {
            warn!(" ex is: {}", ex.pretty(500));
        }

        Examples{datatype: datatype.clone(), examples: res, example_vars: constructor_phs}
    }
}
