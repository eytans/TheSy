pub mod parser {
    use std::fs::File;
    use std::io::Read;
    use std::str::FromStr;

    use egg::{Pattern, RecExpr, Rewrite, SymbolLang, Var, Applier, Searcher, Language, PatternAst, ENodeOrVar, Id};
    use itertools::{Itertools};
    use symbolic_expressions::Sexp;

    use crate::eggstentions::appliers::DiffApplier;
    use crate::lang::{DataType, Function};
    use std::collections::{HashMap};
    use multimap::MultiMap;
    use crate::eggstentions::searchers::multisearcher::{MultiDiffSearcher, EitherSearcher, MultiEqSearcher, FilteringSearcher, MatchFilter, aggregate_conditions, ToDyn, PointerSearcher};
    use std::fmt::Debug;
    use crate::eggstentions::pretty_string::PrettyString;
    use crate::eggstentions::expression_ops::{IntoTree, Tree};
    use crate::thesy::{case_split};
    use crate::tools::tools::combinations;
    use std::rc::Rc;

    #[derive(Default, Clone)]
    pub struct Definitions {
        /// All datatype definitions
        pub datatypes: Vec<DataType>,
        /// All function declereations as (name, type)
        pub functions: Vec<Function>,
        /// Rewrites defined by (assert forall)
        pub rws: Vec<Rewrite<SymbolLang, ()>>,
        /// Terms to prove, given as not forall, (vars - types, precondition, ex1, ex2)
        pub conjectures: Vec<(HashMap<RecExpr<SymbolLang>, RecExpr<SymbolLang>>, Option<RecExpr<SymbolLang>>, RecExpr<SymbolLang>, RecExpr<SymbolLang>)>,
        /// Logic of when to apply case split
        pub case_splitters: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Var, Vec<Pattern<SymbolLang>>)>,
    }

    impl Definitions {
        pub fn merge(&mut self, mut other: Definitions) {
            self.functions.extend_from_slice(&std::mem::take(&mut other.functions).into_iter()
                .filter(|f| self.functions.iter()
                    .all(|f1| f1.name != f.name)).collect_vec());
            self.datatypes.extend_from_slice(&std::mem::take(&mut other.datatypes).into_iter()
                .filter(|d| self.datatypes.iter()
                    .all(|d1| d1.name != d.name)).collect_vec());
            self.conjectures.extend_from_slice(&std::mem::take(&mut other.conjectures).into_iter()
                .filter(|c| !self.conjectures.contains(c)).collect_vec());
            self.rws.extend_from_slice(&std::mem::take(&mut other.rws).into_iter()
                .filter(|rw| {
                    self.rws.iter()
                        .all(|rw1| {
                            rw1.name() != rw.name()
                        })
                }).collect_vec());
            self.case_splitters.extend(std::mem::take(&mut other.case_splitters));
        }
    }

    pub fn parse_file(f: String) -> Definitions {
        let mut file = File::open(f).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        parse(&contents.split("\n").map(|s| s.to_string()).collect_vec()[..])
    }

    fn collected_precon_conds_to_rw(name: String, precond: Option<Pattern<SymbolLang>>, searcher: impl Searcher<SymbolLang, ()> + Debug + 'static, applier: impl Applier<SymbolLang, ()> + 'static, dif_app: bool, conditions: Vec<MatchFilter<SymbolLang, ()>>) -> Result<Rewrite<SymbolLang, ()>, String> {
        if precond.is_some() {
            // Order important as root of match is root of first pattern.
            let dif_searcher = MultiDiffSearcher::new(vec![
                EitherSearcher::left(searcher),
                EitherSearcher::right(MultiEqSearcher::new(vec![precond.unwrap(), Pattern::from_str("true").unwrap()]))
            ]);
            collected_conds_to_rw(name, dif_searcher.into_rc_dyn(), applier, dif_app, conditions)
        } else {
            let dyn_s: Rc<dyn Searcher<SymbolLang, ()>> = Rc::new(searcher);
            collected_conds_to_rw(name, dyn_s, applier, dif_app, conditions)
        }
    }

    fn collected_conds_to_rw(name: String, searcher: Rc<dyn Searcher<SymbolLang, ()>>, applier: impl Applier<SymbolLang, ()> + 'static, dif_app: bool, conditions: Vec<MatchFilter<SymbolLang, ()>>) -> Result<Rewrite<SymbolLang, ()>, String> {
        if !conditions.is_empty() {
            collected_to_rw(name, FilteringSearcher::new(searcher, aggregate_conditions(conditions)).into_rc_dyn(), applier, dif_app)
        } else {
            collected_to_rw(name, searcher, applier, dif_app)
        }
    }

    fn collected_to_rw(name: String, searcher: Rc<dyn Searcher<SymbolLang, ()>>, applier: impl Applier<SymbolLang, ()> + 'static, dif_app: bool) -> Result<Rewrite<SymbolLang, ()>, String> {
        let psearcher = PointerSearcher::new(searcher);
        if dif_app {
            let diff_applier = DiffApplier::new(applier);
            return Rewrite::new(name, psearcher, diff_applier);
        }
        Rewrite::new(name, psearcher, applier)
    }

    pub fn parse(lines: &[String]) -> Definitions {
        // Creating case split rewrites is done per function.
        // Either the body of the function contains ite or the different rewrites
        // span a match expression on a second variable.
        // TODO: Ite variant might not be able to use the conditional apply optimization. Fix.

        // 'Heuristicly' Patterns used for function definitions. Will be used for auto case split.
        let mut function_patterns: MultiMap<Function, PatternAst<SymbolLang>> = MultiMap::new();
        let mut res = Definitions::default();
        let mut name_pats = vec![];
        for l in lines {
            if l.trim().is_empty() || l.starts_with(";") {
                continue;
            }
            let mut sexp = symbolic_expressions::parser::parse_str(l).unwrap();
            let mut l = sexp.take_list().unwrap();
            let name = l[0].take_string().unwrap();
            match name.as_ref() {
                "include" => {
                    let mut to_include = parse_file(format!("theories/{}.th", l[1].take_string().unwrap()));
                    res.merge(to_include);
                }
                "datatype" => {
                    let type_name = l[1].take_string().unwrap();
                    let type_params = l[2].take_list().unwrap();
                    // Constructor name applied on param types
                    let constructors = l[3].take_list().unwrap();
                    res.datatypes.push(DataType::generic(type_name,
                                                         sexp_list_to_recexpr(type_params),
                                                         sexp_list_to_recexpr(constructors)
                                                             .into_iter()
                                                             .map(|e| Function::from(e))
                                                             .collect_vec(),
                    ));
                }
                "declare-fun" => {
                    let fun_name = l[1].take_string().unwrap();
                    let params = sexp_list_to_recexpr(l[2].take_list().unwrap());
                    let return_type = sexp_to_recexpr(&l[3]);
                    res.functions.push(Function::new(fun_name, params, return_type));
                }
                "=>" => {
                    let (name, precondition, mut searcher, applier, conditions) = collect_rule(&mut l);
                    // TODO: case split on precondition?
                    if !searcher.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", searcher.ast.into_tree().root().display_op()), searcher.ast.clone()));
                    }
                    let rw = collected_precon_conds_to_rw(name, precondition, searcher, applier, false, conditions);
                    res.rws.push(rw.unwrap());
                }
                "=|>" => {
                    let (name, precondition, mut searcher, applier, conditions) = collect_rule(&mut l);
                    // TODO: case split on precondition?
                    if !searcher.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", searcher.ast.into_tree().root().display_op()), searcher.ast.clone()));
                    }
                    let rw = collected_precon_conds_to_rw(name, precondition, searcher, applier, true, conditions);
                    res.rws.push(rw.unwrap());
                }
                "<=>" => {
                    let (name, precondition, mut searcher, mut applier, conditions) = collect_rule(&mut l);
                    if !conditions.is_empty() {
                        error!("Can't handle conditions with <=> in {}", name);
                        continue;
                    }
                    // TODO: case split on precondition?
                    if !searcher.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", searcher.ast.into_tree().root().display_op()), searcher.ast.clone()));
                    }
                    if !applier.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", applier.ast.into_tree().root().display_op()), applier.ast.clone()));
                    }
                    let searcher1 = searcher.clone();
                    let applier1 = applier.clone();
                    let rw1 = collected_precon_conds_to_rw(name.clone(), precondition.clone(), searcher, applier, false, conditions);
                    // TODO: Shouldnt need to create empty filter
                    let rw2 = collected_precon_conds_to_rw(name + "-rev", precondition, applier1, searcher1, false, vec![]);
                    let rws = vec![rw1, rw2].into_iter().flatten().collect_vec();
                    res.rws.extend(rws);
                    // buggy macro
                    // res.rws.extend_from_slice(&rewrite!(name; searcher <=> applier));
                }
                "prove" => {
                    let mut forall_list = l[1].take_list().unwrap();
                    assert_eq!(forall_list[0].take_string().unwrap(), "forall");
                    let mut var_map = forall_list[1].take_list().unwrap().iter_mut()
                        .map(|s| {
                            let s_list = s.take_list().unwrap();
                            (sexp_to_recexpr(&s_list[0]), sexp_to_recexpr(&s_list[1]))
                        }).collect();
                    let (mut precondition, mut equality) = {
                        let mut expr = forall_list[2].take_list().unwrap();
                        info!("goal: {}", expr.iter().map(|x| x.to_string()).intersperse(" ".parse().unwrap()).collect::<String>());
                        if expr[0].string().unwrap() == "=>" {
                            let equality = expr.remove(2).take_list().unwrap();
                            let precond = expr.remove(1);
                            (Some(precond), equality)
                        } else {
                            (None, expr)
                        }
                    };
                    if !(equality[0].string().unwrap() == "=" || equality[0].string().unwrap() == "<=>") {
                        equality = vec![Sexp::String("=".to_string()), Sexp::String("true".to_string()), Sexp::List(equality)];
                    }
                    res.conjectures.push((var_map, precondition.map(|x| sexp_to_recexpr(&x)), sexp_to_recexpr(&equality[1]), sexp_to_recexpr(&equality[2])));
                }
                _ => {
                    println!("Error parsing smtlib2 line, found {} op which is not supported", l[0].to_string())
                }
            }
        }

        for (name, pat) in name_pats {
            let opt = res.functions.iter().find(|f| f.name == name);
            if opt.is_some() {
                function_patterns.insert(opt.unwrap().clone(), pat);
            }
        }

        fn get_splitters(datatype: &DataType, root_var: &ENodeOrVar<SymbolLang>) -> Vec<String> {
            datatype.constructors.iter().map(|c|
                if c.params.is_empty() {
                    c.name.clone()
                } else {
                    format!("({} {})", c.name, (0..c.params.len()).map(|i| format!("(param_{}_{} {})", datatype.name, i, root_var.display_op())).join(" "))
                }
            ).collect_vec()
        }

        // Foreach function find if and when case split should be applied
        for f in &res.functions {
            let opt_pats = function_patterns.get_vec(f);
            let case_splitters = opt_pats.map(|pats| {
                let relevant_params = f.params.iter().enumerate().filter_map(|(i, t)| {
                    let param_datatype = res.datatypes.iter().find(|d|
                        d.name == t.into_tree().root().op.to_string());
                    let res = param_datatype.map(|d| (i, t, d));
                    // TODO: also filter by whether the other params are always the same or var and one pattern.
                    // TODO: if there is a pattern use it for screening
                    res.filter(|(i, t, d)|
                        d.constructors.iter().all(|c|
                            pats.iter().any(|p|
                                p.into_tree().children()[*i].root().display_op().to_string() == c.name)))
                });
                let mut x = 0;

                let mut fresh_v = || {
                    x = x + 1;
                    Var::from_str(&*("?autovar".to_string() + &*x.to_string())).unwrap()
                };

                let mut fresh_vars = |exp: RecExpr<ENodeOrVar<SymbolLang>>, vars: &mut HashMap<Var, Var>| {
                    RecExpr::from(exp.as_ref().iter().cloned().map(|e| match e {
                        ENodeOrVar::ENode(n) => { ENodeOrVar::ENode(n) }
                        ENodeOrVar::Var(v) => {
                            if !vars.contains_key(&v) {
                                vars.insert(v, fresh_v());
                            }
                            ENodeOrVar::Var(vars[&v])
                        }
                    }).collect_vec())
                };
                let param_pats = relevant_params.filter_map(|(i, t, d)| {
                    let mut par_pats = (0..f.params.len()).map(|_| vec![]).collect_vec();
                    for p in pats.iter().filter(|p|
                        // Take only patterns where the i param is being matched
                        match p.into_tree().children()[i].root() {
                            ENodeOrVar::ENode(s) => { d.constructors.iter().any(|c| c.name == s.op.to_string()) }
                            ENodeOrVar::Var(_) => { false }
                        }) {
                        let mut vars = HashMap::new();
                        for j in 0..f.params.len() {
                            if i == j { continue; }
                            if let ENodeOrVar::ENode(par_pat) = p.into_tree().children()[j].root() {
                                // replace vars
                                let replaced = fresh_vars(p.into_tree().children()[j].clone().into(), &mut vars);
                                par_pats[j].push(replaced);
                            }
                        }
                    }
                    Some((i, d, par_pats)).filter(|(_, _, ps)| ps.iter().any(|v| !v.is_empty()))
                }).collect_vec();

                param_pats.into_iter().flat_map(|(index, datatype, param_pat)| {
                    let patterns_and_vars = param_pat.into_iter()
                        .map(|v|
                            if v.is_empty() {
                                let mut exp = RecExpr::default();
                                exp.add(ENodeOrVar::Var(fresh_v()));
                                vec![exp]
                            } else {
                                v
                            }).collect_vec();
                    // let mut res: Vec<Rewrite<SymbolLang, ()>> = vec![];
                    let mut res: Vec<(Rc<dyn Searcher<SymbolLang, ()>>, Var, Vec<Pattern<SymbolLang>>)> = vec![];
                    for combs in combinations(patterns_and_vars.iter().cloned().map(|x| x.into_iter())) {
                        let mut nodes = vec![];
                        let children = combs.into_iter().map(|exp| {
                            let cur_len = nodes.len();
                            nodes.extend(exp.as_ref().iter().cloned().map(|s|
                                match s {
                                    ENodeOrVar::ENode(n) => {
                                        ENodeOrVar::ENode(n.map_children(|child| Id::from(usize::from(child) + cur_len)))
                                    }
                                    ENodeOrVar::Var(v) => { ENodeOrVar::Var(v) }
                                }));
                            Id::from(nodes.len() - 1)
                        }).collect_vec();
                        nodes.push(ENodeOrVar::ENode(SymbolLang::new(&f.name, children)));
                        let searcher = Pattern::from(RecExpr::from(nodes));
                        println!("Searcher: {}", searcher.pretty_string());
                        let root_var: &ENodeOrVar<SymbolLang> = searcher.ast.into_tree().children()[index].root();
                        let root_v_opt = if let &ENodeOrVar::Var(v) = root_var {
                            Some(v)
                        } else {
                            None
                        };
                        let mut cond_texts = vec![];
                        let searcher_conditions = datatype.constructors.iter().map(|c| c.apply_params(
                            (0..c.params.len()).map(|i| RecExpr::from_str(&*("?param_".to_owned() + &*i.to_string())).unwrap()).collect_vec()
                        )).map(|exp| {
                            cond_texts.push(format!("Cond(var: {}, pat: {})", root_v_opt.as_ref().unwrap().to_string(), exp.pretty(1000)));
                            FilteringSearcher::create_non_pattern_filterer(Pattern::from_str(&*exp.pretty(1000)).unwrap().into_rc_dyn(), root_v_opt.unwrap())
                        }).collect_vec();
                        let dyn_searcher: Rc<dyn Searcher<SymbolLang, ()>> = Rc::new(searcher.clone());
                        let conditonal_searcher = searcher_conditions.into_iter().fold(dyn_searcher, |pattern, y|{
                            Rc::new(FilteringSearcher::new(pattern, y))
                        });

                        // For now pass the searcher, a condition and expressions for root and
                        // splits. Should be (Searcher, root_var, children_expr, conditions)
                        // res.push(Rewrite::new(rule_name, searcher, DiffApplier::new(ConditionalApplier { applier, condition: cond })).unwrap());
                        res.push((conditonal_searcher.clone(),
                                  root_v_opt.unwrap(),
                                  get_splitters(datatype, root_var).iter().map(|x| Pattern::from_str(x).unwrap()).collect_vec()));
                    }
                    res
                }).collect_vec()
            }).unwrap_or(vec![]);
            res.case_splitters.extend(case_splitters);
        }

        res
    }

    fn collect_rule(l: &mut Vec<Sexp>) -> (String, Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Vec<MatchFilter<SymbolLang, ()>>) {
        let name = l[1].take_string().unwrap();

        let mut conditions_inx = 4;
        // implies
        let (precondition, searcher, applier) = if l[2].is_list() && l[2].list_name().unwrap() == "=>" {
            conditions_inx = 3;
            let mut pre_list = l[2].take_list().unwrap();
            let precondition = Some(Pattern::from_str(&*pre_list[1].to_string()).unwrap());
            let mut equals = pre_list[2].take_list().unwrap();
            assert!(equals[0].take_string().unwrap() == "=");
            let searcher = Pattern::from_str(&*equals[1].to_string()).unwrap();
            let applier = Pattern::from_str(&*equals[2].to_string()).unwrap();
            (precondition, searcher, applier)
        } else {
            let searcher = Pattern::from_str(&*l[2].to_string()).unwrap();
            let applier = Pattern::from_str(&*l[3].to_string()).unwrap();
            (None, searcher, applier)
        };
        let conditions = l[conditions_inx..].iter().map(|s| {
            let v_cond = s.list().unwrap();
            let var = Var::from_str(v_cond[0].string().unwrap()).unwrap();
            let cond: Pattern<SymbolLang> = Pattern::from_str(&*v_cond[1].to_string()).unwrap();
            FilteringSearcher::create_non_pattern_filterer(cond.into_rc_dyn(), var)
        }).collect_vec();
        println!("{} => {}", searcher.pretty_string(), applier.pretty_string());
        (name, precondition, searcher, applier, conditions)
    }

    fn sexp_list_to_recexpr(sexps: Vec<Sexp>) -> Vec<RecExpr<SymbolLang>> {
        sexps.into_iter().map(|e| sexp_to_recexpr(&e)).collect_vec()
    }

    fn sexp_to_recexpr(sexp: &Sexp) -> RecExpr<SymbolLang> {
        RecExpr::from_str(&*sexp.to_string()).unwrap()
    }
}