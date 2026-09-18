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

fn ternary_add_case(nodes: usize) -> (EGraph, [Rewrite; 2]) {
    let mut eg = EGraph::new();
    let atoms: Vec<_> = (0..(2 * nodes + 1))
        .map(|i| eg.atom(&format!("x{i}"), 0))
        .collect();
    let mut term = eg.app("+3", atoms[..3].to_vec());
    for pair in atoms[3..].as_chunks::<2>().0 {
        term = eg.app("+3", vec![term, pair[0], pair[1]]);
    }
    black_box(term);

    let var = Pattern::meta;
    let add = |a, b, c| Pattern::app("+3", vec![a, b, c]);
    let rules = [
        rewrite(
            add(var("?a"), var("?b"), var("?c")),
            add(var("?b"), var("?c"), var("?a")),
        ),
        rewrite(
            add(add(var("?a"), var("?b"), var("?c")), var("?d"), var("?e")),
            add(var("?a"), var("?b"), add(var("?c"), var("?d"), var("?e"))),
        ),
    ];
    (eg, rules)
}

fn sum_swap_case(binders: usize) -> (EGraph, Id, Id, [Rewrite; 1]) {
    let mut eg = EGraph::new();
    let variables: Vec<_> = (0..binders).map(|level| eg.var(binders, level)).collect();
    let mut term = eg.app("a", variables.clone());
    for _ in 0..binders {
        term = eg.lam(term);
        term = eg.app("sum", vec![term]);
    }
    let mut goal = eg.app("a", variables.into_iter().rev().collect());
    for _ in 0..binders {
        goal = eg.lam(goal);
        goal = eg.app("sum", vec![goal]);
    }

    let sum = |body| Pattern::app("sum", vec![Pattern::Lam(Box::new(body))]);
    let rule = rewrite(
        sum(sum(Pattern::miller("?body", vec![1, 0]))),
        sum(sum(Pattern::miller("?body", vec![0, 1]))),
    );
    (eg, term, goal, [rule])
}

fn bench_shape_and_binders(c: &mut Criterion) {
    let mut group = c.benchmark_group("shape-and-binders");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(10))
        .sampling_mode(SamplingMode::Flat);

    group.bench_function("ternary-add-10-nodes-3-rounds", |b| {
        b.iter_batched(
            || ternary_add_case(10),
            // This case exercises three-child nodes without letting the AC
            // closure dwarf the representation choice being measured.
            |(mut eg, rules)| black_box(eg.run(&rules, 3)),
            BatchSize::PerIteration,
        )
    });
    group.bench_function("sum-swap-6-binders", |b| {
        b.iter_batched(
            || sum_swap_case(6),
            |(mut eg, term, goal, rules)| {
                let stats = eg.saturate(&rules);
                assert!(eg.equivalent(&term, &goal));
                black_box(stats)
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

criterion_group!(
    benches,
    bench_ac,
    bench_lambda_under,
    bench_shape_and_binders
);
criterion_main!(benches);
