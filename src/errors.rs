use egg::Id;
use std::error::Error;
use std::fmt::Formatter;

pub type TheSyError = Box<dyn std::error::Error>;

#[derive(Debug)]
pub struct ReconstructError {
    id: Id
}

impl std::fmt::Display for ReconstructError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Reconstruct Error - failed to rebuild {}", self.id)
    }
}

impl Error for ReconstructError {}

impl ReconstructError {
    pub fn new(id: Id) -> TheSyError {
        Box::new(ReconstructError{id})
    }
}