pub mod parser {
    use symbolic_expressions::Sexp;
    use crate::thesy::{DataType, Function};
    use egg::{SymbolLang, Rewrite, RecExpr, Pattern, PatternAst};
    use std::str::FromStr;
    use crate::eggstentions::expression_ops::{IntoTree, RecExpSlice, Tree};
    use itertools::{Itertools, cons_tuples};
    use std::fs::File;
    use std::io::Read;
    use crate::eggstentions::appliers::DiffApplier;

    #[derive(Default, Clone, Debug)]
    pub struct Definitions {
        /// All datatype definitions
        pub datatypes: Vec<DataType>,
        /// All function declereations as (name, type)
        pub functions: Vec<Function>,
        /// Rewrites defined by (assert forall)
        pub rws: Vec<Rewrite<SymbolLang, ()>>,
        /// Terms to prove, given as not forall
        pub conjectures: Vec<(RecExpr<SymbolLang>, RecExpr<SymbolLang>)>
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
            if l.trim().is_empty() {
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
                                                             .collect_vec()

                    ));
                },
                "declare-fun" => {
                    let fun_name = l[1].take_string().unwrap();
                    let params = sexp_list_to_recexpr(l[2].take_list().unwrap());
                    let return_type = sexp_to_recexpr(&l[3]);
                    res.functions.push(Function::new(fun_name, params, return_type));
                },
                "=>" => {
                    let name = l[1].take_string().unwrap();
                    let searcher = Pattern::from_str(&*l[2].to_string()).unwrap();
                    let applier = Pattern::from_str(&*l[3].to_string()).unwrap();
                    res.rws.push(rewrite!(name; searcher => applier));
                },
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
                },
                "=|>" => {
                    let name = l[1].take_string().unwrap();
                    let searcher = Pattern::from_str(&*l[2].to_string()).unwrap();
                    let applier = DiffApplier::new(Pattern::from_str(&*l[3].to_string()).unwrap());
                    println!("{}", applier.pretty(500));
                    res.rws.push(rewrite!(name; searcher => applier));
                },
                "prove" => {
                    res.conjectures.push((sexp_to_recexpr(&l[1]), sexp_to_recexpr(&l[2])));
                }
                _ => {
                    println!("Error parsing smtlib2 line, found {} op which is not supported", l[0].to_string())
                },
            }
        }
        res
    }

    fn sexp_list_to_recexpr(sexps: Vec<Sexp>) -> Vec<RecExpr<SymbolLang>> {
        sexps.into_iter().map(|e| sexp_to_recexpr(&e)).collect_vec()
    }

    fn sexp_to_recexpr(sexp: &Sexp) -> RecExpr<SymbolLang> {
        RecExpr::from_str(&*sexp.to_string()).unwrap()
    }
}