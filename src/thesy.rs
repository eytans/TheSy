use std::rc::Rc;
use crate::tree::Tree;
use egg::{SymbolLang, EGraph, Rewrite, Pattern, Runner};
use std::iter;
use itertools::Itertools;
use crate::eggstentions::multisearcher::multisearcher::MultiDiffSearcher;
use std::str::FromStr;
use std::time::Duration;
use crate::eggstentions::appliers::DiffApplier;

pub struct SyGuESOE {
    // TODO: automatic examples
    examples: Vec<Rc<Tree>>,
    dict: Vec<Rc<Tree>>,
    ind_ph: Rc<Tree>,
    pub egraph: EGraph<SymbolLang, ()>,
    // egraph: EGraph<SymbolLang, ()>,
    // terms: HashMap<Tree, Vec<(Tree, Id)>>,
    sygue_rules: Vec<Rewrite<SymbolLang, ()>>,
}

impl SyGuESOE {
    // TODO: ind from example types
    pub fn new(examples: Vec<Rc<Tree>>, dict: Vec<Rc<Tree>>) -> SyGuESOE {
        let ind_ph = Rc::new(Tree::tleaf(String::from("ind_var"), Rc::new(Some(Tree::leaf(String::from("int"))))));
        let mut egraph = EGraph::default();
        for v in dict.iter().filter(|v| v.subtrees[1].is_leaf()) {
            for (i, e) in Self::iterate_ph_vals(ind_ph.clone(), examples.iter().cloned()).enumerate() {
                let anchor = Self::create_sygue_anchor(i);
                egraph.add_expr(&Tree::branch(anchor.clone(), vec![v.subtrees[0].clone()]).to_rec_expr(None).1);
                egraph.add_expr(&Tree::branch(anchor, vec![e.clone()]).to_rec_expr(None).1);
            }
        }
        let mut res = SyGuESOE {
            examples,
            dict,
            ind_ph,
            egraph,
            sygue_rules: vec![],
        };
        let mut rws = res.create_sygue_rules();
        for rw in rws {
            res.sygue_rules.push(rw);
        }
        res
    }

    fn iterate_ph_vals(ind_ph: Rc<Tree>, examples: impl Iterator<Item=Rc<Tree>>) -> impl Iterator<Item=Rc<Tree>> {
        iter::once(ind_ph).chain(examples)
    }

    fn create_sygue_anchor(i: usize) -> String {
        format!("anchor_{}", i)
    }

    fn iterate_val_cases(&self) -> impl Iterator<Item=Rc<Tree>> {
        let cloned = self.examples.iter().cloned().collect_vec();
        Self::iterate_ph_vals(self.ind_ph.clone(), cloned.into_iter())
    }

    fn create_sygue_rules(&self) -> Vec::<egg::Rewrite<SymbolLang, ()>> {
        self.iterate_val_cases().enumerate().flat_map(|(i, e)| {
            let anchor = SyGuESOE::create_sygue_anchor(i);
            self.dict.iter().zip(iter::once(anchor).cycle()).filter_map(|(f, anchor)| {
                assert_eq!(f.root, "typed");
                let fun_name = &f.subtrees[0].root;
                let fun_type = &f.subtrees[1];
                if fun_type.root != "->" {
                    None
                } else {
                    let patterns = fun_type.subtrees.iter().take(fun_type.subtrees.len() - 1).enumerate()
                        .flat_map(|(i, t)| {
                            let pat_string = format!("({} ?param_{})", anchor, i);
                            vec![
                                Pattern::from_str(&*pat_string).unwrap(),
                                // Pattern::from_str(&*format!("(typed ?param_{} {})", i, t.to_string())).unwrap(),
                            ]
                        }).collect::<Vec<Pattern<SymbolLang>>>();
                    let searcher = MultiDiffSearcher::new(patterns);
                    let param_list = (0..fun_type.subtrees.len() - 1)
                        .map(|i| format!("?param_{}", i))
                        .intersperse(" ".to_string())
                        .collect::<String>();
                    // TODO: Multiapplier under diffapplier with types at result for lists and trees
                    let applier_string = format!("({} ({} {}))", anchor, fun_name, param_list);
                    let applier = DiffApplier::new(Pattern::from_str(&*applier_string).unwrap());
                    Some(Rewrite::new(fun_name, format!("{}_{}", fun_name, anchor), searcher, applier).unwrap())
                }
            })
        }).collect()
    }

    pub fn increase_depth(&mut self) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(1).run(&self.sygue_rules).egraph;
    }

    pub fn equiv_reduc(&mut self, rules: &[Rewrite<SymbolLang, ()>]) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(8).run(rules).egraph;
    }
}