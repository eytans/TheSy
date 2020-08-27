use symbolic_expressions::Sexp;
use std::iter::FromIterator;
use egg::{SymbolLang, RecExpr, Id, EGraph};
use std::fmt::{Display, Formatter};
use cached::proc_macro::cached;

macro_rules! bail {
    ($s:literal $(,)?) => {
        return Err($s.into())
    };
    ($s:literal, $($args:expr),+) => {
        return Err(format!($s, $($args),+).into())
    };
}

#[cached]
fn entry_to_tree(root: String, subentries: Vec<Entry>) -> Tree {
    return Tree::branch(
        root,
        Vec::from_iter(
            subentries.iter().map(|x| entry_to_tree(
                x.symbol.op.to_string(),
                x.subentries.clone()))
        ),
    );
}


#[derive(PartialEq, Eq, Clone, Hash)]
struct Entry {
    symbol: SymbolLang,
    subentries: Vec<Entry>,
}

impl Entry {
    pub fn tree(&self) -> Tree {
        return entry_to_tree(self.symbol.op.to_string(), self.subentries.clone());
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct Tree {
    root: String,
    subtrees: Vec<Tree>,
    typ: Box<Option<Tree>>,
}

impl Tree {
    pub fn leaf(op: String) -> Tree {
        Tree { root: op, subtrees: Vec::new(), typ: Box::new(None) }
    }

    pub fn tleaf(op: String, typ: Box<Option<Tree>>) -> Tree {
        Tree { root: op, subtrees: Vec::new(), typ }
    }

    pub fn branch(op: String, subtrees: Vec<Tree>) -> Tree {
        Tree { root: op, subtrees, typ: Box::new(None) }
    }

    pub fn to_rec_expr(&self, op_res: Option<RecExpr<SymbolLang>>) -> (Id, RecExpr<SymbolLang>) {
        let mut res = if op_res.is_none() { RecExpr::default() } else { op_res.unwrap() };
        return if self.is_leaf() {
            (res.add(SymbolLang::leaf(&self.root)), res)
        } else {
            let mut ids = Vec::default();
            for s in &self.subtrees {
                let (id, r) = s.to_rec_expr(Some(res));
                res = r;
                ids.push(id);
            }
            (res.add(SymbolLang::new(&self.root, ids)), res)
        };
    }

    pub fn add_to_graph(&self, graph: &mut EGraph<SymbolLang, ()>) {
        graph.add_expr(&self.to_rec_expr(None).1);
    }

    pub fn is_leaf(&self) -> bool {
        self.subtrees.is_empty()
    }
}

impl Display for Tree {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_leaf() {
            write!(f, "{}()", &self.root)
        } else {
            if self.subtrees.is_empty() { write!(f, "{}()", &self.root) } else {
                write!(f, "{}({}", &self.root, &self.subtrees[0]);
                for s in self.subtrees.iter().skip(1) {
                    write!(f, ", {}", s);
                }
                write!(f, ")")
            }
        }
    }
}

impl std::str::FromStr for Tree {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        fn parse_sexp_tree(sexp: &Sexp) -> Result<Tree, String> {
            match sexp {
                Sexp::Empty => Err("Found empty s-expression".into()),
                Sexp::String(s) => {
                    Ok(Tree::leaf(s.clone()))
                }
                Sexp::List(list) if list.is_empty() => Err("Found empty s-expression".into()),
                Sexp::List(list) => match &list[0] {
                    Sexp::Empty => unreachable!("Cannot be in head position"),
                    // TODO: add apply
                    Sexp::List(l) => bail!("Found a list in the head position: {:?}", l),
                    Sexp::String(op) if op == "typed" => {
                        let mut tree = parse_sexp_tree(&list[1])?;
                        let types = parse_sexp_tree(&list[2])?;
                        tree.typ = Box::new(Some(types));
                        Ok(tree)
                    }
                    Sexp::String(op) => {
                        let arg_ids = list[1..].iter().map(|s| parse_sexp_tree(s).expect("Parsing should succeed")).collect::<Vec<Tree>>();
                        let node = Tree::branch(op.clone(), arg_ids);
                        Ok(node)
                    }
                },
            }
        }

        let sexp = symbolic_expressions::parser::parse_str(s.trim()).map_err(|e| e.to_string())?;
        Ok(parse_sexp_tree(&sexp)?)
    }
}
