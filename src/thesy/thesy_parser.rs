pub mod parser {
    use std::fs::File;
    use std::io::Read;
    use std::str::FromStr;

    use egg::{Pattern, RecExpr, Rewrite, SymbolLang, Var, Condition, ConditionalApplier};
    use itertools::{Itertools};
    use symbolic_expressions::Sexp;

    use crate::eggstentions::appliers::DiffApplier;
    use crate::lang::{DataType, Function};
    use std::collections::HashMap;
    use crate::eggstentions::conditions::{NonPatternCondition, AndCondition};

    #[derive(Default, Clone, Debug)]
    pub struct Definitions {
        /// All datatype definitions
        pub datatypes: Vec<DataType>,
        /// All function declereations as (name, type)
        pub functions: Vec<Function>,
        /// Rewrites defined by (assert forall)
        pub rws: Vec<Rewrite<SymbolLang, ()>>,
        /// Terms to prove, given as not forall
        pub conjectures: Vec<(HashMap<RecExpr<SymbolLang>, RecExpr<SymbolLang>>, RecExpr<SymbolLang>, RecExpr<SymbolLang>)>,
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
        }
    }

    pub fn parse_file(f: String) -> Definitions {
        let mut file = File::open(f).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();
        parse(&contents.split("\n").map(|s| s.to_string()).collect_vec()[..])
    }

    pub fn parse(lines: &[String]) -> Definitions {
        let mut res = Definitions::default();
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
                    let (name, searcher, mut applier, conditions) = collect_rule(&mut l);
                    if conditions.is_empty() {
                        res.rws.push(rewrite!(name; searcher => applier));
                    } else {
                        let applier = ConditionalApplier { applier, condition: AndCondition::new(conditions) };
                        res.rws.push(rewrite!(name; searcher => applier));
                    }
                }
                "=|>" => {
                    let (name, searcher, applier, conditions) = collect_rule(&mut l);
                    if conditions.is_empty() {
                        let dif_app = DiffApplier::new(applier);
                        res.rws.push(rewrite!(name; searcher => dif_app));
                    } else {
                        let applier = DiffApplier::new(ConditionalApplier { applier, condition: AndCondition::new(conditions) });
                        res.rws.push(rewrite!(name; searcher => applier));
                    }
                }
                "<=>" => {
                    let name = l[1].take_string().unwrap();
                    let searcher: Pattern<SymbolLang> = Pattern::from_str(&*l[2].to_string()).unwrap();
                    let applier: Pattern<SymbolLang> = Pattern::from_str(&*l[3].to_string()).unwrap();
                    let searcher1 = searcher.clone();
                    let applier1 = applier.clone();
                    res.rws.push(rewrite!(name.clone(); searcher => applier));
                    res.rws.push(rewrite!(name + "-rev"; applier1 => searcher1));
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
                    let mut equality = forall_list[2].take_list().unwrap();
                    assert_eq!(equality[0].string().unwrap(), "=");
                    res.conjectures.push((var_map, sexp_to_recexpr(&equality[1]), sexp_to_recexpr(&equality[2])));
                }
                _ => {
                    println!("Error parsing smtlib2 line, found {} op which is not supported", l[0].to_string())
                }
            }
        }
        res
    }

    fn collect_rule(l: &mut Vec<Sexp>) -> (String, Pattern<SymbolLang>, Pattern<SymbolLang>, Vec<Box<dyn Condition<SymbolLang, ()>>>) {
        let name = l[1].take_string().unwrap();
        let searcher = Pattern::from_str(&*l[2].to_string()).unwrap();
        let applier = Pattern::from_str(&*l[3].to_string()).unwrap();
        let conditions = l[4..].iter().map(|s| {
            let v_cond = s.list().unwrap();
            let var = Var::from_str(v_cond[0].string().unwrap()).unwrap();
            let cond: Pattern<SymbolLang> = Pattern::from_str(&*v_cond[1].to_string()).unwrap();
            let res: Box<dyn Condition<SymbolLang, ()>> = Box::new(NonPatternCondition::new(cond, var));
            res
        }).collect_vec();
        (name, searcher, applier, conditions)
    }

    fn sexp_list_to_recexpr(sexps: Vec<Sexp>) -> Vec<RecExpr<SymbolLang>> {
        sexps.into_iter().map(|e| sexp_to_recexpr(&e)).collect_vec()
    }

    fn sexp_to_recexpr(sexp: &Sexp) -> RecExpr<SymbolLang> {
        RecExpr::from_str(&*sexp.to_string()).unwrap()
    }
}