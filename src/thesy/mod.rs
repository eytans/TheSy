pub use {
    example_creator::Examples,
    thesy::TheSy,
};

pub mod thesy;
pub mod example_creator;
pub mod prover;
pub mod statistics;
pub mod case_split;
pub(crate) mod consts;
pub mod semantics;
mod equality_theory;

