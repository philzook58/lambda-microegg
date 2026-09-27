use lambda_microegg::EGraph;

fn main() {
    let mut egraph = EGraph::new_with_proofs();
    let f = egraph.atom("f", 0);
    let a = egraph.atom("a", 0);
    let b = egraph.atom("b", 0);
    let fa = egraph.app(f, a);
    let fb = egraph.app(f, b);
    let g = egraph.atom("g", 0);
    let c = egraph.atom("c", 0);
    let d = egraph.atom("d", 0);
    let _gc = egraph.app(g, c);
    let _gd = egraph.app(g, d);

    egraph.union_assuming(&a, &b, "input equality a = b");
    egraph.union_assuming(&c, &d, "irrelevant equality c = d");
    print!(
        "{}",
        egraph
            .lean_proof(
                "first_order_congruence",
                "{α : Type} (f : α → α) (a b : α)",
                &fa,
                &fb,
            )
            .expect("rebuild proves f a = f b from a = b")
    );
}
