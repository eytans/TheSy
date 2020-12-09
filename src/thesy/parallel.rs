use alloc::boxed::Box;
use egg::{Rewrite, SymbolLang};
use std::sync::mpsc;

/// An enum used for passing messages between threads when running Thesy in parallel mode
pub enum Message{
    IdRulePair(usize, Box<Rewrite<SymbolLang,()>>),                     // intended for sending a rule from thread to main, to let main thread know which thread does not need this rule
    Rule(Box<Rewrite<SymbolLang,()>>),                              // intended for sending a rule from main thread to all other threads, as there is no id needed in this case
    Done(usize),                                                        // not sure if needed, but is used when one thread has done running
}

/// Used for passing data to hooks
pub struct HookData<'a>{
    pub new_rules: &'a [Rewrite<SymbolLang, ()>],
}

// Used in TheSy instances during parallel run
pub struct SenderReceiverWrapper<ReceiveType, SendType>{
    pub tx: mpsc::Sender<ReceiveType>,
    pub rc: mpsc::Receiver<SendType>,
}
// The standard case of SenderReceiverWrapper
pub type MsgSenderReceiverWrapper = SenderReceiverWrapper<Box<Message>,Box<Message>>;
