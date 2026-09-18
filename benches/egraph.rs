use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};
use lambda_microegg::*;
use std::hint::black_box;
use std::time::Duration;

fn rewrite(lhs: Pattern, rhs: Pattern) -> Rewrite {
    Rewrite::new(lhs, rhs).unwrap()
}

fn beta_rule() -> Rewrite {
    rewrite(
        Pattern::app(
            "app",
            vec![
                Pattern::Lam(Box::new(Pattern::miller("?body", vec![0]))),
                Pattern::meta("?arg"),
            ],
        ),
        Pattern::Subst(
            Box::new(Pattern::miller("?body", vec![0])),
            Box::new(Pattern::meta("?arg")),
        ),
    )
}

fn ac_case(n: usize) -> (EGraph, Id, Id, [Rewrite; 2]) {
    let mut eg = EGraph::new();
    let atoms: Vec<_> = (0..n).map(|i| eg.atom(&format!("x{i}"), 0)).collect();
    let mut input = atoms[0];
    for atom in &atoms[1..] {
        input = eg.app("+", vec![input, *atom]);
    }
    let mut goal = atoms[n - 1];
    for atom in atoms[..n - 1].iter().rev() {
        goal = eg.app("+", vec![goal, *atom]);
    }
    let var = Pattern::meta;
    let plus = |a, b| Pattern::app("+", vec![a, b]);
    let rules = [
        rewrite(
            plus(plus(var("?a"), var("?b")), var("?c")),
            plus(var("?a"), plus(var("?b"), var("?c"))),
        ),
        rewrite(plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))),
    ];
    (eg, input, goal, rules)
}

fn bench_ac(c: &mut Criterion) {
    let mut group = c.benchmark_group("associative-commutative");
    // AC10 takes seconds per sample, so use Criterion's minimum sample count
    // and flat sampling rather than increasing the iterations per sample.
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(10))
        .sampling_mode(SamplingMode::Flat);

    for n in [7, 10] {
        group.bench_function(format!("AC{n}"), |b| {
            b.iter_batched(
                || ac_case(n),
                |(mut eg, input, goal, rules)| {
                    let stats = eg.saturate(&rules);
                    assert!(eg.equivalent(&input, &goal));
                    assert_eq!(eg.class_count(), (1 << n) - 1);
                    assert_eq!(
                        eg.node_count(),
                        3usize.pow(n as u32) - 2usize.pow((n + 1) as u32) + 1 + n
                    );
                    black_box(stats)
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
}

fn lambda_under_case() -> (EGraph, Id, [Rewrite; 1], [Rewrite; 1]) {
    let mut eg = EGraph::new();
    let four = eg.atom("4", 1);
    let inner_y = eg.var(2, 1);
    let inner_identity = eg.lam(inner_y);
    let inner_redex = eg.app("app", vec![inner_identity, four]);
    let sum = eg.app("+", vec![four, inner_redex]);
    let term = eg.lam(sum);
    let beta = [beta_rule()];
    let fold = [rewrite(
        Pattern::app("+", vec![Pattern::atom("4"), Pattern::atom("4")]),
        Pattern::atom("8"),
    )];
    (eg, term, beta, fold)
}

fn bench_lambda_under(c: &mut Criterion) {
    c.bench_function("lambda-under", |b| {
        b.iter_batched(
            lambda_under_case,
            |(mut eg, term, beta, fold)| {
                let beta_stats = eg.saturate(&beta);
                let fold_stats = eg.saturate(&fold);
                let result = eg.extract(&term).unwrap();
                assert_eq!(result.to_string(), "(lam 8)");
                black_box((beta_stats, fold_stats))
            },
            BatchSize::PerIteration,
        )
    });
}

criterion_group!(benches, bench_ac, bench_lambda_under);
criterion_main!(benches);
