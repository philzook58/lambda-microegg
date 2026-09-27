use lambda_microegg::{EGraph, Pattern, Rewrite};
use std::time::Instant;

fn main() {
    let mut arguments = std::env::args().skip(1);
    let n: usize = arguments
        .next()
        .as_deref()
        .unwrap_or("5")
        .parse()
        .expect("AC size must be an integer");
    let mode = arguments.next().unwrap_or_else(|| "off".to_owned());
    assert!(n >= 2);
    let mut egraph = match mode.as_str() {
        "off" => EGraph::new(),
        "on" => EGraph::new_with_proofs(),
        _ => panic!("mode must be `off` or `on`"),
    };

    let atoms = (0..n)
        .map(|index| egraph.atom(&format!("x{index}"), 0))
        .collect::<Vec<_>>();
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

    let started = Instant::now();
    let run = egraph.saturate(&rules);
    let saturation = started.elapsed();
    assert!(egraph.equivalent(&input, &goal));
    println!(
        "n={n} mode={mode} saturation_ms={:.3} match_ms={:.3} apply_ms={:.3} rebuild_ms={:.3} rounds={} unions={} classes={} nodes={} raw_ids={} proof={:?}",
        saturation.as_secs_f64() * 1_000.0,
        run.match_time.as_secs_f64() * 1_000.0,
        run.apply_time.as_secs_f64() * 1_000.0,
        run.rebuild_time.as_secs_f64() * 1_000.0,
        run.rounds,
        run.unions,
        egraph.class_count(),
        egraph.node_count(),
        egraph.raw_id_count(),
        egraph.proof_stats(),
    );
}
