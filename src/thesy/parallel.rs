use std::boxed::Box;
use egg::{Rewrite, SymbolLang, Runner, Pattern, EGraph};
use std::sync::mpsc;
use spmc;
use crate::thesy::TheSy;
use std::vec;
use std::str::FromStr;
use spmc::RecvError;
use z3_sys::ParamKind::Symbol;
extern crate owning_ref;

/// An enum used for passing messages between threads when running Thesy in parallel mode
pub enum Message{
    //IdRulePair(usize, Box<Rewrite<SymbolLang,()>>),                     // intended for sending a rule from thread to main, to let main thread know which thread does not need this rule
    //Rule(Box<Rewrite<SymbolLang,()>>),                              // intended for sending a rule from main thread to all other threads, as there is no id needed in this case
    IdRulePair(usize, RewriteInfo),
    Rule(RewriteInfo),
    Done(usize),                                                        // not sure if needed, but is used when one thread has done running
}

/// Used for passing data to hooks
pub struct HookData<'a>{
    pub rules_to_send: &'a [Rewrite<SymbolLang, ()>],
    pub rules_received: Vec<Rewrite<SymbolLang,()>>,
}

#[derive(Clone)]
pub struct RewriteInfo{
    pub name: String,
    pub long_name: String,
    pub searcher: Pattern<SymbolLang>,
    pub applier: Pattern<SymbolLang>,
}

impl RewriteInfo{
    pub fn new_from_rewrite(rw: &Rewrite<SymbolLang,()>) -> RewriteInfo{
        RewriteInfo{
            name : rw.name().to_string(),
            long_name : rw.long_name().to_string(),
            searcher : **rw.searcher().clone(),
            applier : **rw.applier().clone(),
        }
    }

    pub fn as_rewrite(&self) -> Rewrite<SymbolLang,()>{
        Rewrite::new(self.name.clone(), self.long_name.clone(),
                     self.searcher.clone(),
                     self.applier.clone()).unwrap()
    }

    pub fn into_rewrite(self) -> Rewrite<SymbolLang,()>{
        Rewrite::new(self.name, self.long_name,
                     self.searcher,
                     self.applier).unwrap()
    }
}

impl From<Rewrite<SymbolLang, ()>> for RewriteInfo {
    fn from(_: Rewrite<SymbolLang, ()>) -> Self {
        unimplemented!()
    }
}
// The standard case of SenderReceiverWrapper
pub type MsgSenderReceiverWrapper = SenderReceiverWrapper<Box<Message>,Box<Message>>;

impl From<RewriteInfo> for Rewrite<SymbolLang, ()> {
    fn from(_: RewriteInfo) -> Self {
        unimplemented!()
    }
}

/// Used in TheSy instances during parallel run
pub struct SenderReceiverWrapper<'a, ReceiveType, SendType> {
    pub tx: &'a mut mpsc::Sender<ReceiveType>,
    pub rc: &'a mut mpsc::Receiver<SendType>,
}

impl <'a, ReceiveType, SendType> SenderReceiverWrapper<'a, ReceiveType, SendType> {
    // fn (&mut Self, &HookData, &mut MsgSenderReceiverWrapper) -> Result<(), String>>>,
    // //after_inference_hooks: Vec<Box<dyn FnMut(&mut Self, &Vec<(Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Rewrite<SymbolLang, ()>)>) -> Result<(), String>>>,
    //
    // /// the hooks are used before every step of TheSy which could expand the rules set
    // /// currently used to support parallel running
    // before_inference_hooks: Vec<Box<dyn FnMut(&mut Self, &mut Vec<Rewrite<SymbolLang, ()>>, &mut MsgSenderReceiverWrapper) -> Result<(), String>>>,
    // /// hooks passed to [runner]
    // /// for more info check: [EGG] documentation
    // equiv_reduc_hooks: Vec<Box<dyn FnMut(&mut Runner<SymbolLang,()>) -> Result<(), String>>>,
}

/// The standard case of SenderReceiverWrapper
pub type MsgSenderReceiverWrapper<'a> = SenderReceiverWrapper<'a, Box<Message>,Box<Message>>;

/// returns a tuple with each of the hooks necessary to run TheSy parallel
/// first returned value are hooks for before_inference_hooks
/// second returned value are hooks for after_inference_hooks
/// third returned value are hooks for equiv_reduc_hooks
pub fn insert_parallel_hooks(thesy :&mut TheSy,
                            mut thread_rc: spmc::Receiver<Box<Message>>,
                            mut thread_tx: mpsc::Sender<Box<Message>>,
                            id: usize) -> //(Vec<Box<dyn FnMut(&mut TheSy) -> Result<(), String>>>,
                                                                                         // Vec<Box<dyn FnMut(&mut TheSy) -> Result<(), String>>>,
                                                                                         // Vec<Box<dyn FnMut(&mut Runner<SymbolLang,()>) -> Result<(), String>>>)
                                                                                                                  (){

    thesy.with_before_inference_hook(|thesy, rules|{
        let mut rule_vec = vec![];
        loop{
            match thread_rc.try_recv(){
                Err(_) => {
                    break;
                },
                Ok(boxed_msg) => {
                    // TODO: before adding rule to list check if the rule is already in this instance
                    match *boxed_msg{
                      Message::Rule(rw_info) => {
                          rule_vec.push(rw_info.into_rewrite());
                      },
                      _ => {
                          warn!("sent non-rule message to thread");
                      }
                    }

                },
                _ => {}
            }
        }
        rules.append(&mut rule_vec);
        Result::Ok(())
    });
    let mut last_index = 0;
    let id = id;
    thesy.with_after_inference_hook(move |thesy, rules|{
        rules[last_index..].iter().for_each(|rule|{
            thread_tx.send(Box::new(Message::IdRulePair(id, RewriteInfo::new_from_rewrite(rule))));                 // TODO: might be wrong and need to use into_str or something like that
        });
        last_index = rules.len();
        Ok(())
    });

    // thesy.with_equiv_reduc_hook(|runner: Runner<SymbolLang, (), ()>|{
    //    // TODO: after change of Runner, implement hook here so we can send and receive hooks when running equivalence reduction
    // });
}