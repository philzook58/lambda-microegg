use lambda_microegg::{EGraph, Pattern, Rewrite};

fn main() {
    let mut egraph = EGraph::new_with_proofs();
    let x = egraph.atom("x", 0);
    let zero = egraph.atom("zero", 0);
    let inner = egraph.apps("plus", vec![x, zero]);
    let outer = egraph.apps("plus", vec![inner, zero]);
    let rule = Rewrite::named(
        "r1",
        Pattern::apps("plus", vec![Pattern::meta("?a"), Pattern::atom("zero")]),
        Pattern::meta("?a"),
    )
    .unwrap();

    egraph.saturate(&[rule]);
    print!(
        "{}",
        egraph
            .lean_proof(
                "two_rewrites",
                "{α : Type} (app : α → α → α) (plus zero x : α) \
                 (r1 : ∀ a, app (app plus a) zero = a)",
                &outer,
                &x,
            )
            .unwrap()
    );
}
