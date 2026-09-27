use lambda_microegg::{EGraph, Pattern, Rewrite};
use std::time::Instant;

fn main() {
    let started = Instant::now();
    let mut egraph = EGraph::new_with_proofs();
    let atoms: Vec<_> = (0..7)
        .map(|index| egraph.atom(&format!("x{index}"), 0))
        .collect();
    let mut input = atoms[0];
    for atom in &atoms[1..] {
        input = egraph.apps("plus", vec![input, *atom]);
    }
    let mut goal = atoms[6];
    for atom in atoms[..6].iter().rev() {
        goal = egraph.apps("plus", vec![goal, *atom]);
    }
    let var = Pattern::meta;
    let plus = |left, right| Pattern::apps("plus", vec![left, right]);
    let rules = [
        Rewrite::new(
            plus(plus(var("?a"), var("?b")), var("?c")),
            plus(var("?a"), plus(var("?b"), var("?c"))),
        )
        .unwrap(),
        Rewrite::new(plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))).unwrap(),
    ];
    let setup = started.elapsed();
    let saturation_started = Instant::now();
    egraph.saturate(&rules);
    let saturation = saturation_started.elapsed();
    assert!(egraph.equivalent(&input, &goal));
    let render_started = Instant::now();
    let certificate = egraph
        .lean_proof(
            "ac7",
            "{α : Type} (app : α → α → α) (plus x0 x1 x2 x3 x4 x5 x6 : α)",
            &input,
            &goal,
        )
        .unwrap();
    let render = render_started.elapsed();
    eprintln!(
        "setup={setup:?} saturation={saturation:?} render={render:?} bytes={}",
        certificate.len()
    );
    print!("{certificate}");
}
