pub mod thesy;
pub mod example_creator;
pub mod thesy_parser;
mod prover;
pub mod statistics;

pub use {
    thesy::TheSy,
    example_creator::examples,
    thesy_parser::parser,
};
