use alloc::boxed::Box;
use egg::{Rewrite, SymbolLang};


/// An enum used for passing messages between threads when running Thesy in parallel mode
pub enum Message{
    IdRulePair(usize, Box<Rewrite<SymbolLang,()>>),                     // intended for sending a rule from thread to main, to let main thread know which thread does not need this rule
    Rule(Box<Rewrite<SymbolLang,()>>),                              // intended for sending a rule from main thread to all other threads, as there is no id needed in this case
    Done(usize),                                                        // not sure if needed, but is used when one thread has done running
}
