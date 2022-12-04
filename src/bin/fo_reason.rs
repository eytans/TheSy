use std::fs::File;
use egg::*;
use structopt::StructOpt;

#[derive(StructOpt)]
struct CliOpt {
    /// The path to the file to read
    #[structopt(parse(from_os_str))]
    path: std::path::PathBuf
}

fn main() {
    let args = CliOpt::from_args();

    let mut fi = File::open(args.path).unwrap();
    let (mut g, pal) = //EGraph::<SymbolLang, ()>::from_tuples_int(tup.iter());
        EGraph::<SymbolLang, ()>::from_tuples_text(&mut fi).unwrap();
    let rw = [
        vec![rewrite!(":+ []"; "(:+ [] ?y)" => "(:: ?y [])")],
        rewrite!(":+ ::"; "(:+ (:: ?x ?xs) ?y)" <=> "(:: ?x (:+ ?xs ?y))"),
        vec![rewrite!("rev []"; "(rev [])" => "[]")],
        vec![rewrite!("rev ::"; "(rev (:: ?x ?xs))" => "(:+ (rev ?xs) ?x)")/*,
             rewrite!("rev ::%"; "(:+ (rev ?xs) ?x)" => "(rev (:: ?x ?xs))")*/],
        vec![rewrite!("+ 0"; "(+ 0 ?x)" => "(?x)")],
        rewrite!("+ S"; "(+ (S ?x) ?y)" <=> "(S (+ ?x ?y))")
    ].concat();
    /*
    let exp1: RecExpr<SymbolLang> = RecExpr::from_str("(:: y (rev l))").unwrap();
    let exp2: RecExpr<SymbolLang> = RecExpr::from_str("(rev (:+ l y))").unwrap();
    let u1 = g.add_expr(&exp1);
    let u2 = g.add_expr(&exp2);*/
    /*
    let c = g.create_color();
    let cons = g.colored_add_expr(c, &RecExpr::from_str("(:: x xs)").unwrap());
    let l = g.add_expr(&RecExpr::from_str("l").unwrap());
    g.colored_union(c, cons, l);
    let v1 = g.add_expr(&RecExpr::from_str("(:: y (rev xs))").unwrap());
    let v2 = g.add_expr(&RecExpr::from_str("(rev (:+ xs y))").unwrap());
    g.colored_union(c, v1, v2);
    g.rebuild();*/
    g = Runner::default().with_egraph(g).run(&rw).egraph;
    g.dot().to_png("/tmp/thesy-out.png").unwrap();
    //println!("{:#?}", g.get_color(c).unwrap());`

    g.to_tuples_text(&pal, &mut std::io::stdout()).unwrap();
}
