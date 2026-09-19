use criterion::{BatchSize, Criterion, SamplingMode, criterion_group, criterion_main};
use lambda_microegg::*;
use std::hint::black_box;
use std::time::Duration;

fn rewrite(lhs: Pattern, rhs: Pattern) -> Rewrite {
    Rewrite::new(lhs, rhs).unwrap()
}

fn beta_rule() -> Rewrite {
    rewrite(
        Pattern::fo_app(
            "app",
            vec![
                Pattern::binder("lam", Pattern::miller("?body", vec![0])),
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
        input = eg.fo_app("+", vec![input, *atom]);
    }
    let mut goal = atoms[n - 1];
    for atom in atoms[..n - 1].iter().rev() {
        goal = eg.fo_app("+", vec![goal, *atom]);
    }
    let var = Pattern::meta;
    let plus = |a, b| Pattern::fo_app("+", vec![a, b]);
    let rules = [
        rewrite(
            plus(plus(var("?a"), var("?b")), var("?c")),
            plus(var("?a"), plus(var("?b"), var("?c"))),
        ),
        rewrite(plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))),
    ];
    (eg, input, goal, rules)
}

/// The same AC problem using `[+ a b]`, represented as two `HOApp` nodes,
/// instead of the first-order `(+ a b)` node used by `ac_case`.
fn hoapp_ac_case(n: usize) -> (EGraph, Id, Id, [Rewrite; 2]) {
    fn plus(eg: &mut EGraph, op: Id, left: Id, right: Id) -> Id {
        let function = eg.ho_app(op, left);
        eg.ho_app(function, right)
    }

    let mut eg = EGraph::new();
    let op = eg.atom("+", 0);
    let atoms: Vec<_> = (0..n).map(|i| eg.atom(&format!("x{i}"), 0)).collect();
    let mut input = atoms[0];
    for atom in &atoms[1..] {
        input = plus(&mut eg, op, input, *atom);
    }
    let mut goal = atoms[n - 1];
    for atom in atoms[..n - 1].iter().rev() {
        goal = plus(&mut eg, op, goal, *atom);
    }

    let var = Pattern::meta;
    let plus = |left, right| Pattern::ho_app(Pattern::ho_app(Pattern::atom("+"), left), right);
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
    group.bench_function("AC10-hoapp", |b| {
        b.iter_batched(
            || hoapp_ac_case(10),
            |(mut eg, input, goal, rules)| {
                let stats = eg.saturate(&rules);
                assert!(eg.equivalent(&input, &goal));
                // In addition to the ordinary AC expression classes, HOApp
                // has one partial-application class `[+ term]` for every
                // possible proper left subset and one class for the `+` atom.
                assert_eq!(eg.class_count(), 2 * (1 << 10) - 2);
                assert_eq!(
                    eg.node_count(),
                    3usize.pow(10) - 2usize.pow(11) + 1 + 10 + (1 << 10) - 1
                );
                black_box(stats)
            },
            BatchSize::PerIteration,
        )
    });
    group.finish();
}

fn lambda_under_case() -> (EGraph, Id, [Rewrite; 1], [Rewrite; 1]) {
    let mut eg = EGraph::new();
    let four = eg.atom("4", 1);
    let inner_y = eg.var(2, 1);
    let inner_identity = eg.binder("lam", inner_y);
    let inner_redex = eg.fo_app("app", vec![inner_identity, four]);
    let sum = eg.fo_app("+", vec![four, inner_redex]);
    let term = eg.binder("lam", sum);
    let beta = [beta_rule()];
    let fold = [rewrite(
        Pattern::fo_app("+", vec![Pattern::atom("4"), Pattern::atom("4")]),
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
                assert_eq!(result.to_string(), "(@lam 8)");
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
    let mut term = eg.fo_app("+3", atoms[..3].to_vec());
    for pair in atoms[3..].as_chunks::<2>().0 {
        term = eg.fo_app("+3", vec![term, pair[0], pair[1]]);
    }
    black_box(term);

    let var = Pattern::meta;
    let add = |a, b, c| Pattern::fo_app("+3", vec![a, b, c]);
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
    let mut term = eg.fo_app("a", variables.clone());
    for _ in 0..binders {
        term = eg.binder("sum", term);
    }
    let mut goal = eg.fo_app("a", variables.into_iter().rev().collect());
    for _ in 0..binders {
        goal = eg.binder("sum", goal);
    }

    let sum = |body| Pattern::binder("sum", body);
    let rule = rewrite(
        sum(sum(Pattern::miller("?body", vec![1, 0]))),
        sum(sum(Pattern::miller("?body", vec![0, 1]))),
    );
    (eg, term, goal, [rule])
}

/// A deep chain of distinct e-classes beneath one context variable. Each link
/// is its own e-class, so this isolates traversal cost over many classes from
/// the combinatorial blowup the AC cases measure.
fn chain_case(depth: usize) -> (EGraph, Id, Id) {
    let mut eg = EGraph::new();
    let mut body = eg.var(1, 0);
    for i in 0..depth {
        // Alternate the operator so no two links hash-cons together.
        body = eg.fo_app(if i % 2 == 0 { "f" } else { "g" }, vec![body]);
    }
    let replacement = eg.atom("c", 0);
    (eg, body, replacement)
}

/// Already-substituted chain of the given depth, ready to extract.
fn extraction_chain_case(depth: usize) -> (EGraph, Id) {
    let (mut eg, body, replacement) = chain_case(depth);
    let result = eg.substitute(&body, 0, &replacement);
    (eg, result)
}

fn bench_substitution(c: &mut Criterion) {
    let mut group = c.benchmark_group("substitution");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(10))
        .sampling_mode(SamplingMode::Flat);

    // Deliberately no extraction inside the timed region: extraction of a
    // chain this deep costs an order of magnitude more than the substitution
    // and would be all this measured. Correctness is covered by the tests.
    for depth in [200, 800] {
        group.bench_function(format!("chain-{depth}"), |b| {
            b.iter_batched(
                || chain_case(depth),
                |(mut eg, body, replacement)| black_box(eg.substitute(&body, 0, &replacement)),
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
}

fn bench_extraction(c: &mut Criterion) {
    let mut group = c.benchmark_group("extraction");
    group
        .sample_size(10)
        .warm_up_time(Duration::from_secs(1))
        .measurement_time(Duration::from_secs(10))
        .sampling_mode(SamplingMode::Flat);

    for depth in [200, 400, 800] {
        group.bench_function(format!("chain-{depth}"), |b| {
            b.iter_batched(
                || extraction_chain_case(depth),
                |(mut eg, result)| {
                    let term = eg.extract(&result).unwrap();
                    assert_eq!(term.size(), depth + 1);
                    black_box(term)
                },
                BatchSize::PerIteration,
            )
        });
    }
    group.finish();
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
    bench_substitution,
    bench_extraction,
    bench_shape_and_binders
);
criterion_main!(benches);
