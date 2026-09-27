use lambda_microegg::{EGraph, Pattern, Rewrite};
use std::time::Instant;

fn main() {
    let mut egraph = EGraph::new_with_proofs();
    let atoms: Vec<_> = (0..3)
        .map(|index| egraph.atom(&format!("x{index}"), 0))
        .collect();
    let input_pair = egraph.apps("plus", vec![atoms[0], atoms[1]]);
    let input = egraph.apps("plus", vec![input_pair, atoms[2]]);
    let goal_pair = egraph.apps("plus", vec![atoms[1], atoms[0]]);
    let goal = egraph.apps("plus", vec![atoms[2], goal_pair]);
    let var = Pattern::meta;
    let plus = |left, right| Pattern::apps("plus", vec![left, right]);
    let rules = [
        Rewrite::named(
            "assoc",
            plus(plus(var("?a"), var("?b")), var("?c")),
            plus(var("?a"), plus(var("?b"), var("?c"))),
        )
        .unwrap(),
        Rewrite::named(
            "comm",
            plus(var("?a"), var("?b")),
            plus(var("?b"), var("?a")),
        )
        .unwrap(),
    ];

    let saturation_started = Instant::now();
    egraph.saturate(&rules);
    let saturation = saturation_started.elapsed();
    assert!(egraph.equivalent(&input, &goal));
    let trace = egraph.proof_stats().unwrap();
    let render_started = Instant::now();
    let certificate = egraph
        .lean_proof(
            "ac3",
            "{α : Type} (plus : α → α → α) (x0 x1 x2 : α) \
             (assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)) \
             (comm : ∀ a b, plus a b = plus b a)",
            &input,
            &goal,
        )
        .unwrap();
    let render = render_started.elapsed();
    eprintln!(
        "saturation={saturation:?} render={render:?} trace={trace:?} bytes={}",
        certificate.len()
    );
    print!("{certificate}");
}
