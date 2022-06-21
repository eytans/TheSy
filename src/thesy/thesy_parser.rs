mod parser {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;
    use std::fs::File;
    use std::io::Read;
    use std::path::Display;
    use std::rc::Rc;
    use std::str::FromStr;

    use egg::{Applier, ENodeOrVar, Id, Language, Pattern, PatternAst, RecExpr, Rewrite, Searcher, SymbolLang, Var};
    use itertools::Itertools;
    use multimap::MultiMap;
    use smallvec::alloc::fmt::Formatter;
    use symbolic_expressions::{Sexp, SexpError};

    use crate::eggstentions::appliers::DiffApplier;
    use crate::eggstentions::expression_ops::{IntoTree, Tree};
    use crate::eggstentions::pretty_string::PrettyString;
    use crate::eggstentions::searchers::multisearcher::{aggregate_conditions, EitherSearcher, FilteringSearcher, MatchFilter, MultiDiffSearcher, MultiEqSearcher, PointerSearcher, ToDyn};
    use crate::lang::{DataType, Function};
    use crate::thesy::case_split;
    use crate::thesy::thesy_parser::parser::TheSyParseErr::IOError;
    use crate::thesy::semantics::Definitions;
    use crate::thesy::thesy_parser::parser::TheSyParseErr::UnknownError;
    use crate::tools::tools::combinations;

    #[derive(Debug)]
    pub enum TheSyParseErr {
        UnknownError,
        IOError(std::io::Error),
        SexpError(SexpError),
    }

    impl Error for TheSyParseErr {}

    impl std::fmt::Display for TheSyParseErr {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            let mut res = writeln!(f, "Error during thesy parsing");
            if res.is_ok() {
                if let IOError(x) = self {
                    res = std::fmt::Display::fmt(&x, f);
                }
            }
            res
        }
    }

    fn parse_file(f: String) -> Result<Definitions, TheSyParseErr> {
        let mut file = File::open(f);
        let mut contents = String::new();
        file.and_then(|mut f| f.read_to_string(&mut contents)).map_err(|x| IOError(x))
            .and_then(|_| parse(&contents.split("\n").map(|s| s.to_string()).collect_vec()[..]))
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

    fn parse(lines: &[String]) -> Result<Definitions, TheSyParseErr> {
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

            let mut sexp = symbolic_expressions::parser::parse_str(l);
            if !(sexp.is_ok() && sexp.iter().all(|s| s.is_list())) {
                continue;
            }
            let mut l = sexp.unwrap().take_list().unwrap();
            let name = l[0].take_string();
            if name.is_err() {
                continue;
            }
            let mut defs = Definitions::default();
            let temp: Result<Definitions, TheSyParseErr> = match name.unwrap().as_ref() {
                "include" => {
                    parse_file(format!("theories/{}.th", l[1].take_string().unwrap()))
                }
                "datatype" => {
                    if !(l.len() > 3 && l[1].is_string() && l[2].is_list() && l[3].is_list()) {
                        continue;
                    }
                    let type_name = l[1].take_string().unwrap();
                    let type_params = l[2].take_list().unwrap();
                    // Constructor name applied on param types
                    let constructors = l[3].take_list().unwrap();
                    defs.datatypes.push(DataType::generic(type_name,
                                                         sexp_list_to_recexpr(type_params),
                                                         sexp_list_to_recexpr(constructors)
                                                             .into_iter()
                                                             .map(|e| Function::from(e))
                                                             .collect_vec(),
                    ));
                    Ok(defs)
                }
                "declare-fun" => {
                    let fun_name = l[1].take_string();
                    let return_type = sexp_to_recexpr(&l[3]);
                    let params = l[2].take_list();
                    if fun_name.is_ok() && params.is_ok() {
                        defs.functions.push(Function::new(fun_name.unwrap(), sexp_list_to_recexpr(params.unwrap()), return_type));
                        Ok(defs)
                    } else {
                        fun_name.and_then(|_| params.and_then(|_| Ok(defs))).map_err(|e| TheSyParseErr::SexpError(e))
                    }
                }
                "=>" => {
                    let rules = collect_rule(&mut l);
                    if rules.is_err() {
                        continue;
                    }
                    let (name, precondition, mut searcher, applier, conditions) = rules.unwrap();
                    // TODO: case split on precondition?
                    if !searcher.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", searcher.ast.into_tree().root().display_op()), searcher.ast.clone()));
                    }
                    let rw = collected_precon_conds_to_rw(name, precondition, searcher, applier, false, conditions);
                    defs.rws.push(rw.unwrap());
                    Ok(defs)
                }
                "=|>" => {
                    let rules = collect_rule(&mut l);
                    if rules.is_err() {
                        continue;
                    }
                    let (name, precondition, mut searcher, applier, conditions) = rules.unwrap();
                    // TODO: case split on precondition?
                    if !searcher.ast.into_tree().root().is_leaf() {
                        name_pats.push((format!("{}", searcher.ast.into_tree().root().display_op()), searcher.ast.clone()));
                    }
                    let rw = collected_precon_conds_to_rw(name, precondition, searcher, applier, true, conditions);
                    defs.rws.push(rw.unwrap());
                    Ok(defs)
                }
                "<=>" => {
                    let rules = collect_rule(&mut l);
                    if rules.is_err() {
                        continue;
                    }
                    let (name, precondition, mut searcher, applier, conditions) = rules.unwrap();
                    if !conditions.is_empty() {
                        error!("Can't handle conditions with <=> in {}", name);
                        return Err(UnknownError);
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
                    defs.rws.extend(rws);
                    Ok(defs)
                    // buggy macro
                    // res.rws.extend_from_slice(&rewrite!(name; searcher <=> applier));
                }
                "prove" => {
                    if !(l[1].is_list() && l[1].list().unwrap().len() > 2 && l[1].list().unwrap()[0].is_string()) {
                        continue;
                    }
                    let mut forall_list = l[1].take_list().unwrap();
                    assert_eq!(forall_list[0].take_string().unwrap(), "forall");
                    if !(forall_list[1].is_list() && forall_list[1].list().unwrap().iter().all(|s| s.is_list())) {
                        continue;
                    }
                    let mut var_map = forall_list[1].take_list().unwrap().iter_mut()
                        .map(|s| {
                            let s_list = s.take_list().unwrap();
                            (sexp_to_recexpr(&s_list[0]), sexp_to_recexpr(&s_list[1]))
                        }).collect();
                    let (mut precondition, mut equality) = {
                        if !forall_list[2].is_list() {
                            continue;
                        }
                        let mut expr = forall_list[2].take_list().unwrap();
                        info!("goal: {}", expr.iter().map(|x| x.to_string()).intersperse(" ".parse().unwrap()).collect::<String>());
                        if !expr[0].is_string() {
                            continue;
                        }
                        if expr[0].string().unwrap() == "=>" {
                            if expr.len() < 3 || !expr[2].is_list() {
                                continue;
                            }
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
                    defs.conjectures.push((var_map, precondition.map(|x| sexp_to_recexpr(&x)), sexp_to_recexpr(&equality[1]), sexp_to_recexpr(&equality[2])));
                    Ok(defs)
                }
                _ => {
                    println!("Error parsing smtlib2 line, found {} op which is not supported", l[0].to_string());
                    Err(UnknownError)
                }
            };
            if temp.is_ok() {
                res.merge(temp.unwrap());
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

                let mut fresh_vars = |exp: RecExpr<ENodeOrVar<SymbolLang>>, vars: &mut IndexMap<Var, Var>| {
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
                        let mut vars = IndexMap::new();
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
                        let conditonal_searcher = searcher_conditions.into_iter().fold(dyn_searcher, |pattern, y| {
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

        Ok(res)
    }

    fn collect_rule(l: &mut Vec<Sexp>) -> Result<(String, Option<Pattern<SymbolLang>>, Pattern<SymbolLang>, Pattern<SymbolLang>, Vec<MatchFilter<SymbolLang, ()>>), TheSyParseErr> {
        if !l[1].is_string() {
            return Err(UnknownError);
        }
        let name = l[1].take_string().unwrap();

        let mut conditions_inx = 4;
        // implies
        let (precondition, searcher, applier) = {
            if l[2].is_list() && l[2].list().unwrap()[0].is_string() && l[2].list_name().unwrap() == "=>" {
                conditions_inx = 3;
                let mut pre_list = l[2].take_list().unwrap();
                let pat_res = Pattern::from_str(&*pre_list[1].to_string());
                if pat_res.is_err() || !pre_list[2].is_list() {
                    return Err(UnknownError);
                }
                let precondition = Some(pat_res.unwrap());
                let mut equals = pre_list[2].take_list().unwrap();
                if !(equals[0].is_string() && equals[0].take_string().unwrap() == "=") {
                    return Err(UnknownError);
                }
                // TODO: Error manage patterns
                let searcher = Pattern::from_str(&*equals[1].to_string());
                let applier = Pattern::from_str(&*equals[2].to_string());
                if searcher.is_err() || applier.is_err() {
                    return Err(UnknownError);
                }
                (precondition, searcher.unwrap(), applier.unwrap())
            } else {
                // TODO: Error manage patterns
                let searcher = Pattern::from_str(&*l[2].to_string());
                let applier = Pattern::from_str(&*l[3].to_string());
                if searcher.is_err() || applier.is_err() {
                    return Err(UnknownError);
                }
                (None, searcher.unwrap(), applier.unwrap())
            }
        };
        if l[conditions_inx..].iter().any(|x| !(x.is_list() && x.list().unwrap().len() > 1 && x.list().unwrap()[0].is_string() && x.list().unwrap()[1].is_string())) {
            return Err(UnknownError);
        }
        let conditions = l[conditions_inx..].iter().map(|s| {
            let v_cond = s.list().unwrap();
            let var = Var::from_str(v_cond[0].string().unwrap()).unwrap();
            let cond: Pattern<SymbolLang> = Pattern::from_str(&*v_cond[1].to_string()).unwrap();
            FilteringSearcher::create_non_pattern_filterer(cond.into_rc_dyn(), var)
        }).collect_vec();
        println!("{} => {}", searcher.pretty_string(), applier.pretty_string());
       Ok((name, precondition, searcher, applier, conditions))
    }

    fn sexp_list_to_recexpr(sexps: Vec<Sexp>) -> Vec<RecExpr<SymbolLang>> {
        sexps.into_iter().map(|e| sexp_to_recexpr(&e)).collect_vec()
    }

    fn sexp_to_recexpr(sexp: &Sexp) -> RecExpr<SymbolLang> {
        RecExpr::from_str(&*sexp.to_string()).unwrap()
    }
}