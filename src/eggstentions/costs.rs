use egg::{CostFunction, SymbolLang, Id};
use std::collections::HashSet;
use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RepOrder {
    vars: HashSet<String>,
    depth: usize,
    size: usize,
}

impl PartialOrd for RepOrder {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        unimplemented!()
    }
}

pub struct MinRep;
impl CostFunction<SymbolLang> for MinRep {
    /// The `Cost` type. It only requires `PartialOrd` so you can use
    /// floating point types, but failed comparisons (`NaN`s) will
    /// result in a panic.
    /// We choose to count
    type Cost = RepOrder;

    /// Calculates the cost of an enode whose children are `Cost`s.
    ///
    /// For this to work properly, your cost function should be
    /// _monotonic_, i.e. `cost` should return a `Cost` greater than
    /// any of the child costs of the given enode.
    fn cost<C>(&mut self, enode: &SymbolLang, costs: C) -> Self::Cost where
        C: FnMut(Id) -> Self::Cost {
        unimplemented!()
    }
}