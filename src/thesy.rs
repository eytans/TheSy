use std::rc::Rc;
use crate::tree::Tree;
use egg::{SymbolLang, EGraph, Rewrite, Pattern, Runner, Searcher, Var, Id, Subst, RecExpr, Extractor};
use std::iter;
use itertools::Itertools;
use crate::eggstentions::multisearcher::multisearcher::MultiDiffSearcher;
use std::str::FromStr;
use std::time::{Duration, SystemTime};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

pub struct SyGuESOE {
    // TODO: automatic examples
    examples: Vec<Rc<Tree>>,
    dict: Vec<Rc<Tree>>,
    ind_ph: Rc<Tree>,
    pub egraph: EGraph<SymbolLang, ()>,
    searchers: HashMap<String, (MultiDiffSearcher, Vec<Var>)>,
    example_ids: HashMap<Id, Vec<Id>>,
    // egraph: EGraph<SymbolLang, ()>,
    // terms: HashMap<Tree, Vec<(Tree, Id)>>,
    // sygue_rules: Vec<Rewrite<SymbolLang, ()>>,
}

impl SyGuESOE {
    // TODO: ind from example types
    pub fn new(examples: Vec<Rc<Tree>>, dict: Vec<Rc<Tree>>) -> SyGuESOE {
        let ind_ph = Rc::new(Tree::tleaf(String::from("ind_var"), Rc::new(Some(Tree::leaf(String::from("int"))))));
        let mut egraph = EGraph::default();
        let anchor = Self::create_sygue_anchor();
        let mut example_ids = HashMap::new();
        let ind_id = ind_ph.add_to_graph(&mut egraph);
        egraph.add(SymbolLang::new(anchor.clone(), vec![ind_id]));
        let initial_example_ids = examples.iter()
            .map(|e| e.add_to_graph(&mut egraph)).collect_vec();
        example_ids.insert(ind_id, initial_example_ids);
        for v in dict.iter().filter(|v| v.subtrees[1].is_leaf()) {
            let id = v.subtrees[0].add_to_graph(&mut egraph);
            egraph.add(SymbolLang::new(anchor.clone(), vec![id]));
            example_ids.insert(id, Vec::from_iter(iter::repeat(id).take(examples.len())));
        }

        let mut res = SyGuESOE {
            examples,
            dict,
            ind_ph,
            egraph,
            // sygue_rules: vec![],
            searchers: HashMap::new(),
            example_ids,
        };
        // let mut rws = res.create_sygue_rules();
        // for rw in rws {
        //     res.sygue_rules.push(rw);
        // }
        res.searchers = res.create_sygue_serchers();
        res.egraph.rebuild();
        res
    }

    // fn extract_classes(&self) -> HashSet<RecExpr<SymbolLang>> {
        // let ext = Extractor::new(&self.egraph, );
        // self.
    // }

    fn create_sygue_anchor() -> String {
        format!("sygueanchor")
    }

    fn create_sygue_serchers(&self) -> HashMap<String, (MultiDiffSearcher, Vec<Var>)> {
        let mut res = HashMap::new();
        self.dict.iter().for_each(|f| {
            assert_eq!(f.root, "typed");
            let fun_name = &f.subtrees[0].root;
            let fun_type = &f.subtrees[1];
            if fun_type.root == "->" {
                let params: Vec<Var> = (0..fun_type.subtrees.len() - 1).map(|i| Var::from_str(&*format!("?param_{}", i)).unwrap()).collect_vec();
                let anchor = SyGuESOE::create_sygue_anchor();
                let patterns = fun_type.subtrees.iter().take(fun_type.subtrees.len() - 1).enumerate()
                    .flat_map(|(i, t)| {
                        let pat_string = format!("({} ?param_{})", anchor, i);
                        vec![
                            Pattern::from_str(&*pat_string).unwrap(),
                            // Pattern::from_str(&*format!("(typed ?param_{} {})", i, t.to_string())).unwrap(),
                        ]
                    }).collect::<Vec<Pattern<SymbolLang>>>();
                res.insert(fun_name.clone(), (MultiDiffSearcher::new(patterns), params));
            }
        });
        res
    }

    pub fn increase_depth(&mut self) {
        // How to efficiently find who merged? Extract one from each ph class then check for its
        // id the sets of ids the examples are in.
        // Meaning need to hold all ids for ph and reference it to relevant example ids
        // You have base case. Create all new ids, for each example lookup params, create edge find all ids from edge
        // Add anchor only to ind_ph term

        // First we need to update our keys as they might not be relevant anymore
        self.example_ids = self.example_ids.iter()
            .map(|(k, v)| (self.egraph.find(*k), v.iter().map(|x| self.egraph.find(*x)).collect())).collect();
        // Now apply for all matches
        let anchor = Self::create_sygue_anchor();
        fn create_edge(op: &String, params: &Vec<Var>, sub: &Subst) -> SymbolLang {
            SymbolLang::new(op.clone(), params.iter().map(|v| sub.get(v.clone()).unwrap()).copied().collect())
        }

        // TODO: can probably remove graph
        fn translate_edge(edge: &SymbolLang, e_index: usize, translations: &HashMap<Id, Vec<Id>>) -> SymbolLang {
            let new_child = edge.children.iter().map(|id| {
                translations[id][e_index]
            }).collect_vec();
            SymbolLang::new(edge.op.clone(), new_child)
        }
        let length = self.examples.len();

        let op_matches = self.searchers.iter()
            .map(|(op, (searcher, params))| {
                (op, params, searcher.search(&self.egraph).iter_mut().flat_map(|mut sm| std::mem::take(&mut sm.substs)).collect_vec())
            }).collect_vec();
        for (op, params, subs) in op_matches {
            for sub in subs {
                // Foreach match add a term for ind_ph and foreach example and update example_ids map
                let new_edge = create_edge(op, params, &sub);
                let key = self.egraph.add(new_edge.clone());
                self.egraph.add(SymbolLang::new(anchor.clone(), vec![key]));
                let mut new_ids = vec![];
                for i in 0..length {
                    new_ids.push(self.egraph.add(translate_edge(&new_edge, i, &self.example_ids)));
                }
                self.example_ids.insert(key, new_ids);
            }
        }
        self.egraph.rebuild();
    }

    pub fn equiv_reduc(&mut self, rules: &[Rewrite<SymbolLang, ()>]) {
        self.egraph = Runner::default().with_time_limit(Duration::from_secs(60 * 60)).with_node_limit(60000).with_egraph(std::mem::take(&mut self.egraph)).with_iter_limit(8).run(rules).egraph;
    }
}

#[cfg(test)]
mod test {
    use crate::thesy::SyGuESOE;
    use crate::tree::Tree;
    use std::rc::Rc;
    use std::str::FromStr;
    use std::time::SystemTime;
    use itertools::Itertools;
    use std::collections::HashSet;
    use egg::{SymbolLang, Pattern, Searcher};

    fn create_nat_sygue() -> SyGuESOE {
        SyGuESOE::new(
            vec!["Z", "(S Z)", "(S (S Z))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ph0 int)", "(typed ph1 int)", "(typed Z int)", "(typed S (-> int int))", "(typed pl (-> int int int))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        )
    }

    #[test]
    fn test_no_double_ids() {
        // Note: this is a little slower then usual as there is no equivalence reduction.
        let mut syg = create_nat_sygue();
        let start = SystemTime::now();
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
        syg.increase_depth();
        println!("current time (milies): {}", SystemTime::now().duration_since(start).unwrap().as_millis());
        assert!(syg.egraph.classes().all(|c| c.nodes.len() == 1));
    }

    #[test]
    fn no_double_translation() {
        // from previous test assume each class has one edge
        let mut syg = create_nat_sygue();
        let start = SystemTime::now();
        syg.increase_depth();
        syg.increase_depth();
        let level0 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() == 0)
            .map(|c| (c.id, c.nodes[0].clone()))
            .collect_vec();
        let edges_level0 = level0.iter().map(|c| &c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level0.len(), level0.len());
        let level1 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level1 = level1.iter().map(|c| c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level1.len(), level1.len());
        let level2 = syg.egraph.classes()
            .filter(|c| c.nodes[0].children.iter().any(|n| level1.iter().find(|x| x.0 == *n).is_some()))
            .filter(|c| c.nodes[0].children.len() > 0 || c.nodes[0].children.iter().all(|n| level0.iter().find(|x| x.0 == *n).is_some() || level1.iter().find(|x| x.0 == *n).is_some()))
            .map(|c| (c.id, &c.nodes[0]))
            .collect_vec();
        let edges_level2 = level2.iter().map(|c| c.1).collect::<HashSet<&SymbolLang>>();
        assert_eq!(edges_level2.len(), level2.len());
    }

    #[test]
    fn test_creates_expected_terms_nat() {
        let mut syg = create_nat_sygue();
        let z = syg.egraph.lookup(SymbolLang::new("Z", vec![]));
        assert!(z.is_some());
        let sz = syg.egraph.lookup(SymbolLang::new("S", vec![z.unwrap()]));
        assert!(sz.is_some());
        let ssz = syg.egraph.lookup(SymbolLang::new("S", vec![sz.unwrap()]));
        assert!(ssz.is_some());
        let ind_ph = syg.egraph.lookup(SymbolLang::new(syg.ind_ph.root.clone(), vec![]));
        assert!(ind_ph.is_some());
        let ph1 = syg.egraph.lookup(SymbolLang::new("ph0", vec![]));
        assert!(ph1.is_some());
        let ph2 = syg.egraph.lookup(SymbolLang::new("ph1", vec![]));
        assert!(ph2.is_some());
        syg.increase_depth();
        let pl_ph1_ex2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ph1.unwrap()), syg.egraph.find(ssz.unwrap())]));
        assert!(pl_ph1_ex2.is_some());
        let pl_ind_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(ind_ph.unwrap()), syg.egraph.find(ph2.unwrap())]));
        assert!(pl_ind_ph2.is_some());
        let s_ph2 = syg.egraph.lookup(SymbolLang::new("S", vec![syg.egraph.find(ph2.unwrap())]));
        assert!(s_ph2.is_some());
        syg.increase_depth();
        let pl_pl_ph1_ex2_ph2 = syg.egraph.lookup(SymbolLang::new("pl", vec![syg.egraph.find(pl_ph1_ex2.unwrap()), syg.egraph.find(ssz.unwrap())]));
        assert!(pl_pl_ph1_ex2_ph2.is_some());
    }

    #[test]
    fn does_not_create_unneeded_terms() {
        let mut syg = SyGuESOE::new(
            vec!["Z"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ph0 int)", "(typed S (-> int int))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(sygueanchor ?x)").unwrap();
        let results0 = anchor_patt.search(&syg.egraph);
        assert_eq!(2usize, results0.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(4usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        assert_eq!(6usize, anchor_patt.search(&syg.egraph).iter().map(|x| x.substs.len()).sum());

        let mut syg = SyGuESOE::new(
            vec!["Z"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
            vec!["(typed ph0 int)", "(typed ph1 int)", "(typed x (-> int int int))"].into_iter().map(|s| Rc::new(Tree::from_str(s).unwrap())).collect(),
        );

        let anchor_patt: Pattern<SymbolLang> = Pattern::from_str("(sygueanchor ?x)").unwrap();
        let results0 = anchor_patt.search(&syg.egraph);
        assert_eq!(3usize, results0.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        let results1 = anchor_patt.search(&syg.egraph);
        assert_eq!(12usize, results1.iter().map(|x| x.substs.len()).sum());
        syg.increase_depth();
        let results2 = anchor_patt.search(&syg.egraph);
        assert_eq!(147usize, results2.iter().map(|x| x.substs.len()).sum());
    }

    // TODO: test on lists
}