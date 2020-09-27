use egg::{RecExpr, SymbolLang};
use crate::eggstentions::expression_ops::{IntoTree, Tree};
use crate::thesy_parser::parser::Definitions;
use std::collections::{HashSet, HashMap};
use crate::thesy::DataType;
use itertools::Itertools;

/// For now I will create full examples?
/// Will be very expensive for trees but will deal with that later
pub fn examples(datatype: &DataType, max_depth: usize) -> Vec<RecExpr<SymbolLang>> {
    let mut ph_counts: HashMap<RecExpr<SymbolLang>, usize> = HashMap::new();
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
        let last_example = res.last().unwrap().clone();
         res.extend(constructors.iter().map(|constr| {
            // Creating example by creating ph and using as params.
            // Reusing old examples, doesn't matter how we build them so for now straight forward.
            constr.apply_params(constr.params.iter()
                .map(|p| {
                    // Comparing trees is more safe
                    if p.into_tree() == datatype.as_exp().into_tree() {
                        last_example.clone()
                    } else {
                        let index = *ph_counts.entry(p.clone()).or_insert(0);
                        *ph_counts.get_mut(p).unwrap() += 1;
                        format!("autovar_{}_{}", p.into_tree().to_spaceless_string(), index).parse().unwrap()
                    }
                }).collect_vec())
        }));
    }
    for ex in res.iter() {
        println!(" ex is: {}", ex.pretty(500));
    }
    res
}
