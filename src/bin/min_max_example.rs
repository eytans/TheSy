use egg::{EGraph, Rewrite, SymbolLang};

fn main() {
    let mut g: EGraph<SymbolLang, ()> = EGraph::default();
    // Add all needed expressions:
    // true
    // false
    // max(x, y) - min(x, y)
    // abs(x - y)
    // x < y
    let t = g.add_expr(&"true".parse().unwrap());
    // let f = g.add_expr(&"false".parse().unwrap());
    let x = g.add_expr(&"x".parse().unwrap());
    let y = g.add_expr(&"y".parse().unwrap());
    let maxxy = g.add_expr(&"(max x y)".parse().unwrap());
    let minus = g.add_expr(&"(- (max x y) (min x y))".parse().unwrap());
    let minxy = g.add_expr(&"(min x y)".parse().unwrap());
    let abs = g.add_expr(&"(abs (- x y))".parse().unwrap());
    let lt = g.add_expr(&"(< x y)".parse().unwrap());
    g.rebuild();
    g.dot().to_dot("init_min_max.dot").unwrap();

    // Now create all rewrite rules
    // {?x} < {?y} \Rightarrow \tmin({?x}, {?y}) \rwto {?x} \\
    // \lnot{?x} < {?y} \Rightarrow \tmin({?x}, {?y}) \rwto {?y} \\
    // {?x} < {?y} \Rightarrow \tmax({?x}, {?y}) \rwto {?y} \\
    // \lnot{?x} < {?y} \Rightarrow \tmax({?x}, {?y}) \rwto {?x} \\
    // {?x} < {?y} \Rightarrow |{?x} - {?y}| \rwto {?y} - {x?} \\
    // \lnot{?x} < {?y} \Rightarrow |{?x} - {?y}| \rwto {?x} - {?y} \\

    // let mut rws: Vec<Rewrite<SymbolLang, ()>> = vec![];
    // rws.push(egg::multi_rewrite!("mindef"; "?r = (min x y), ?b = (< x y), ?b = true" => "?r = x"));
    // rws.push(egg::multi_rewrite!("minnotdef"; "?r = (min x y), ?b = (< x y), ?b = false" => "?r = y"));
    // rws.push(egg::multi_rewrite!("maxdef"; "?r = (max x y), ?b = (< x y), ?b = true" => "?r = y"));
    // rws.push(egg::multi_rewrite!("maxnotdef"; "?r = (max x y), ?b = (< x y), ?b = false" => "?r = x"));
    // rws.push(egg::multi_rewrite!("absdef"; "?r = (abs (- x y)), ?b = (< x y), ?b = true" => "?r = (- y x)"));
    // rws.push(egg::multi_rewrite!("absnotdef"; "?r = (abs (- x y)), ?b = (< x y), ?b = false" => "?r = (- x y)"));

    // Add color and start running
    let blue = g.create_color(None);
    // g.colored_union(blue, lt, f);
    g.colored_union(blue, lt, t);
    g.rebuild();
    g.colored_dot(blue).to_dot("init_b_min_max.dot").unwrap();
    // g.colored_dot(blue).set_print_color("red".to_string()).to_dot("init_b_min_max.dot").unwrap();

    // Run one iteration - This is actually not good because it rebuilds, and we need the middle step
    // let runner = egg::Runner::default().with_egraph(g).with_iter_limit(1).run(&rws);
    // let mut g = runner.egraph;

    // Manually "Applying rules" by union
    g.colored_union(blue, minxy, x);
    g.colored_union(blue, maxxy, y);
    // g.colored_union(blue, minxy, y);
    // g.colored_union(blue, maxxy, x);
    let minusyx = g.add_expr(&"(- y x)".parse().unwrap());
    // let minusxy = g.add_expr(&"(- x y)".parse().unwrap());
    // g.colored_union(blue, abs, minusxy);
    g.colored_union(blue, abs, minusyx);
    // g.colored_dot(blue).set_print_color("red".to_string()).to_dot("rw_b_min_max.dot").unwrap();
    g.colored_dot(blue).to_dot("rw_b_min_max.dot").unwrap();

    // Rebuild
    g.rebuild();
    g.colored_dot(blue).to_dot("after_b_min_max.dot").unwrap();
    // g.colored_dot(blue).set_print_color("red".to_string()).to_dot("after_b_min_max.dot").unwrap();
}
