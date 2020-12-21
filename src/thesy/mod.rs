pub mod thesy;
pub mod example_creator;
pub mod thesy_parser;
mod prover;
pub mod statistics;
mod case_split;
mod consts;

pub use {
    thesy::TheSy,
    example_creator::examples,
    thesy_parser::parser,
    case_split::case_split_all,
};
