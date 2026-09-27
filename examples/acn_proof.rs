use lambda_microegg::{EGraph, Pattern, Rewrite};
use std::time::Instant;

fn main() {
    let n: usize = std::env::args()
        .nth(1)
        .as_deref()
        .unwrap_or("3")
        .parse()
        .expect("AC size must be an integer");
    assert!(n >= 2);
    let mut egraph = EGraph::new_with_proofs();
    let atoms: Vec<_> = (0..n)
        .map(|index| egraph.atom(&format!("x{index}"), 0))
        .collect();
    let mut input = atoms[0];
    for atom in &atoms[1..] {
        input = egraph.apps("plus", vec![input, *atom]);
    }
    let mut goal = atoms[0];
    for atom in &atoms[1..] {
        goal = egraph.apps("plus", vec![*atom, goal]);
    }
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
    let arena = egraph.proof_stats().unwrap();
    let atom_binders = (0..n)
        .map(|index| format!("x{index}"))
        .collect::<Vec<_>>()
        .join(" ");
    let binders = format!(
        "{{α : Type}} (plus : α → α → α) ({atom_binders} : α) \
         (assoc : ∀ a b c, plus (plus a b) c = plus a (plus b c)) \
         (comm : ∀ a b, plus a b = plus b a)"
    );
    let render_started = Instant::now();
    let certificate = egraph
        .lean_proof(&format!("ac{n}"), &binders, &input, &goal)
        .unwrap();
    let render = render_started.elapsed();
    eprintln!(
        "n={n} saturation={saturation:?} render={render:?} arena={arena:?} bytes={}",
        certificate.len()
    );
    print!("{certificate}");
}
