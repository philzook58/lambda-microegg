use lambda_microegg::*;

#[path = "../src/frontend.rs"]
mod frontend;
use frontend::*;

fn beta_rule() -> Rewrite {
    Rewrite::new(
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
    .expect("beta rewrite is well formed")
}

#[derive(Clone, Debug)]
enum ReferenceTerm {
    Var(usize),
    Atom(&'static str),
    App(&'static str, Vec<ReferenceTerm>),
    Lam(Box<ReferenceTerm>),
}

fn next_random(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    *state
}

fn generated_term(ctx: usize, depth: usize, state: &mut u64) -> ReferenceTerm {
    let choice = next_random(state) as usize;
    if depth == 0 {
        return if ctx > 0 && choice.is_multiple_of(2) {
            ReferenceTerm::Var(choice % ctx)
        } else {
            ReferenceTerm::Atom(["a", "b", "0"][choice % 3])
        };
    }
    match choice % 5 {
        0 if ctx > 0 => ReferenceTerm::Var(choice % ctx),
        1 => ReferenceTerm::Atom(["a", "b", "0"][choice % 3]),
        2 => ReferenceTerm::Lam(Box::new(generated_term(ctx + 1, depth - 1, state))),
        3 => ReferenceTerm::App("f", vec![generated_term(ctx, depth - 1, state)]),
        _ => ReferenceTerm::App(
            "pair",
            vec![
                generated_term(ctx, depth - 1, state),
                generated_term(ctx, depth - 1, state),
            ],
        ),
    }
}

fn add_reference(eg: &mut EGraph, term: &ReferenceTerm, ctx: usize) -> Id {
    match term {
        ReferenceTerm::Var(level) => eg.var(ctx, *level),
        ReferenceTerm::Atom(name) => eg.atom(name, ctx),
        ReferenceTerm::App(op, children) => {
            let children = children
                .iter()
                .map(|child| add_reference(eg, child, ctx))
                .collect();
            eg.app(op, children)
        }
        ReferenceTerm::Lam(body) => {
            let body = add_reference(eg, body, ctx + 1);
            eg.lam(body)
        }
    }
}

fn embed_reference(term: &ReferenceTerm, root_ctx: usize, extra: usize) -> ReferenceTerm {
    match term {
        ReferenceTerm::Var(level) => {
            ReferenceTerm::Var(level + usize::from(*level >= root_ctx) * extra)
        }
        ReferenceTerm::Atom(name) => ReferenceTerm::Atom(name),
        ReferenceTerm::App(op, children) => ReferenceTerm::App(
            op,
            children
                .iter()
                .map(|child| embed_reference(child, root_ctx, extra))
                .collect(),
        ),
        ReferenceTerm::Lam(body) => {
            ReferenceTerm::Lam(Box::new(embed_reference(body, root_ctx, extra)))
        }
    }
}

fn substitute_reference(
    term: &ReferenceTerm,
    variable: usize,
    replacement: &ReferenceTerm,
    replacement_ctx: usize,
    local_depth: usize,
) -> ReferenceTerm {
    match term {
        ReferenceTerm::Var(level) if *level == variable => {
            embed_reference(replacement, replacement_ctx, local_depth)
        }
        ReferenceTerm::Var(level) => ReferenceTerm::Var(level - usize::from(*level > variable)),
        ReferenceTerm::Atom(name) => ReferenceTerm::Atom(name),
        ReferenceTerm::App(op, children) => ReferenceTerm::App(
            op,
            children
                .iter()
                .map(|child| {
                    substitute_reference(child, variable, replacement, replacement_ctx, local_depth)
                })
                .collect(),
        ),
        ReferenceTerm::Lam(body) => ReferenceTerm::Lam(Box::new(substitute_reference(
            body,
            variable,
            replacement,
            replacement_ctx,
            local_depth + 1,
        ))),
    }
}

#[test]
fn bundled_sexp_demos_run() {
    let demo_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("demos");
    let mut demos: Vec<_> = std::fs::read_dir(&demo_dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "sexp")
        })
        .collect();
    demos.sort();
    assert!(!demos.is_empty());

    for path in demos {
        let input = std::fs::read_to_string(&path).unwrap();
        if let Err(error) = run_sexp_script(&input) {
            panic!("{} failed: {error}", path.display());
        }
    }
}

fn egg_simple_rules() -> Vec<Rewrite> {
    let var = Pattern::meta;
    let app = |op, left, right| Pattern::app(op, vec![left, right]);
    let rewrite = |lhs, rhs| Rewrite::new(lhs, rhs).unwrap();
    vec![
        rewrite(
            app("+", var("?a"), var("?b")),
            app("+", var("?b"), var("?a")),
        ),
        rewrite(
            app("*", var("?a"), var("?b")),
            app("*", var("?b"), var("?a")),
        ),
        rewrite(app("+", var("?a"), Pattern::atom("0")), var("?a")),
        rewrite(app("*", var("?a"), Pattern::atom("0")), Pattern::atom("0")),
        rewrite(app("*", var("?a"), Pattern::atom("1")), var("?a")),
    ]
}
#[test]
fn sexp_frontend_runs_insert_rewrite_run_extract() {
    let output = run_sexp_script(
        r#"
            ; Commands may be separated by arbitrary whitespace.
            (insert (+ a 0))
            (rewrite (+ ?x 0) ?x)
            (run 10)
            (extract (+ a 0))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "a");
    assert!(output[2].starts_with("; ran 1 rounds,"));
}
#[test]
fn sexp_frontend_rewrites_under_a_binder() {
    let output = run_sexp_script(
        r#"
            (insert (lam x (f a)))
            (rewrite (f ?x) ?x)
            (run 10)
            (extract (lam x (f a)))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "(lam x0 a)");
}
#[test]
fn sexp_frontend_parses_context_variables_and_reports_scope_errors() {
    let output = run_sexp_script("(insert (lam x x)) (extract (lam x x))").unwrap();
    assert_eq!(output.last().unwrap(), "(lam x0 x0)");
    assert!(
        run_sexp_script("(insert $0)")
            .unwrap_err()
            .contains("out of scope")
    );
}
#[test]
fn named_binders_support_shadowing_and_namespaced_indices() {
    let output = run_sexp_script(
        r#"
            (insert (lam x (lam x x)))
            (extract (lam x (lam x x)))
            (insert (lam x (lam x x@1)))
            (extract (lam x (lam x x@1)))
        "#,
    )
    .unwrap();
    assert_eq!(output[1], "(lam x0 (lam x1 x1))");
    assert_eq!(output[3], "(lam x0 (lam x1 x0))");
}
#[test]
fn dollar_variables_always_refer_to_the_outer_context() {
    let output =
        run_sexp_script("(insert 1 (lam x (pair $0 x))) (extract 1 (lam x (pair $0 x)))").unwrap();
    assert_eq!(output.last().unwrap(), "(lam x0 (pair $0 x0))");
}
#[test]
fn named_output_quotes_atoms_that_would_be_captured() {
    let output = run_sexp_script("(insert (lam x x0)) (extract (lam x x0))").unwrap();
    assert_eq!(output.last().unwrap(), "(lam x0 \"x0\")");
}
#[test]
fn lambda_names_are_alpha_irrelevant() {
    let output = run_sexp_script("(guard (lam x x) (lam y y))").unwrap();
    assert_eq!(output, ["; guard passed"]);
}
#[test]
fn sexp_frontend_honors_zero_run_limit() {
    let output =
        run_sexp_script("(insert (f a)) (rewrite (f ?x) ?x) (run 0) (extract (f a))").unwrap();
    assert!(output[2].starts_with("; ran 0 rounds, 0 unions: 2 classes, 2 e-nodes\n"));
    assert!(output[2].contains("; match "));
    assert_eq!(output.last().unwrap(), "(f a)");
}
#[test]
fn sexp_reset_clears_terms_and_rewrite_rules() {
    let output = run_sexp_script(
        r#"
            (insert old)
            (rewrite (f ?x) ?x)
            (reset)
            (match ?x)
            (insert (f a))
            (run 4)
            (extract (f a))
        "#,
    )
    .unwrap();
    assert_eq!(output[2], "; reset");
    assert_eq!(output[3], "; no matches");
    assert_eq!(output.last().unwrap(), "(f a)");
}
#[test]
fn sexp_reset_clears_substitution_rewrites() {
    let output = run_sexp_script(
        r#"
            (rewrite (app (lam x (?body x)) ?arg) (#subst (?body x) x ?arg))
            (reset)
            (insert (app (lam x x) a))
            (run 4)
            (extract (app (lam x x) a))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "(app (lam x0 x0) a)");
}
#[test]
fn sexp_reset_rejects_arguments() {
    assert_eq!(
        run_sexp_script("(reset now)").unwrap_err(),
        "line 1:1: wrong number of arguments to 'reset'"
    );
}
#[test]
fn sexp_union_equates_two_terms() {
    let output = run_sexp_script("(union (f a) b) (extract (f a))").unwrap();
    assert_eq!(output, ["; unioned", "b"]);
}
#[test]
fn sexp_union_supports_an_ambient_context() {
    let output = run_sexp_script("(union 1 (f $0) $0) (extract 1 (f $0))").unwrap();
    assert_eq!(output, ["; unioned", "$0"]);
}
#[test]
fn sexp_union_reports_existing_equality() {
    let output = run_sexp_script("(union a a)").unwrap();
    assert_eq!(output, ["; already equivalent"]);
}
#[test]
fn sexp_subst_builtin_is_available_in_insert_and_outer_contexts() {
    let output = run_sexp_script(
        r#"
            (insert 0 (#subst $0 $0 fred))
            (guard (#subst $0 $0 fred) fred)
            (insert 1 (#subst (pair $0 x) x a))
            (extract 1 (pair $0 a))
        "#,
    )
    .unwrap();
    assert_eq!(output[1], "; guard passed");
    assert_eq!(output.last().unwrap(), "(pair $0 a)");
}
#[test]
fn sexp_subst_builtin_is_available_in_union() {
    let output = run_sexp_script(
        r#"
            (union (#subst (f x) x a) b)
            (guard (f a) b)
        "#,
    )
    .unwrap();
    assert_eq!(output, ["; unioned", "; guard passed"]);
}
#[test]
fn sexp_guard_accepts_an_established_equality() {
    let output = run_sexp_script("(union (f a) b) (guard (f a) b)").unwrap();
    assert_eq!(output, ["; unioned", "; guard passed"]);
}
#[test]
fn sexp_guard_checks_equality_after_saturation() {
    let output =
        run_sexp_script("(insert (* a 0)) (rewrite (* ?x 0) 0) (run 4) (guard (* a 0) 0)").unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}
#[test]
fn sexp_guard_supports_an_ambient_context() {
    let output = run_sexp_script("(union 1 (f $0) $0) (guard 1 (f $0) $0)").unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}
#[test]
fn sexp_guard_fails_the_script_for_unequal_terms() {
    let error = run_sexp_script("(guard (f a) b)").unwrap_err();
    assert_eq!(error, "line 1:1: guard failed: (f a) != b");
}

#[test]
fn sexp_fail_accepts_a_failing_command() {
    let output = run_sexp_script("(fail (guard (f a) b))\n(echo continued)").unwrap();
    assert_eq!(
        output,
        [
            "; failed as expected: guard failed: (f a) != b",
            "; continued"
        ]
    );
}

#[test]
fn sexp_fail_rejects_a_successful_command() {
    let error = run_sexp_script("\n(fail (guard a a))").unwrap_err();
    assert_eq!(error, "line 2:1: wrapped command succeeded");
}

#[test]
fn sexp_fail_discards_the_wrapped_commands_state() {
    let output = run_sexp_script("(fail (guard (f a) b)) (match ?x)").unwrap();
    assert_eq!(
        output,
        [
            "; failed as expected: guard failed: (f a) != b",
            "; no matches"
        ]
    );
}

#[test]
fn sexp_fail_checks_its_arity() {
    assert_eq!(
        run_sexp_script("(fail)").unwrap_err(),
        "line 1:1: wrong number of arguments to 'fail'"
    );
}

#[test]
fn sexp_errors_report_source_lines() {
    let error = run_sexp_script("(echo ok)\n\n(guard a b)").unwrap_err();
    assert_eq!(error, "line 3:1: guard failed: a != b");

    let error = run_sexp_script("(echo ok)\n(insert (f a)").unwrap_err();
    assert_eq!(error, "line 2:1: unclosed '('");

    let error = run_sexp_script("(echo ok)\n)").unwrap_err();
    assert_eq!(error, "line 2:1: unexpected ')'");
}
#[test]
fn sexp_match_prints_every_extracted_substitution() {
    let output = run_sexp_script(
        r#"
            (insert (f a))
            (insert (f b))
            (match (f ?x))
        "#,
    )
    .unwrap();
    assert_eq!(
        &output[2..],
        ["; match 1 ctx0 |-> {?x = a}", "; match 2 ctx0 |-> {?x = b}"]
    );
}
#[test]
fn sexp_match_prints_miller_substitutions() {
    let output = run_sexp_script(
        r#"
            (insert (lam x x))
            (match (lam x ?a))
            (match (lam x (?a x)))
        "#,
    )
    .unwrap();
    assert_eq!(output[1], "; no matches");
    assert_eq!(output[2], "; match 1 ctx0 |-> {?a = mlam x0 x0}");
}
#[test]
fn sexp_match_prints_miller_parameters_on_the_right() {
    let output = run_sexp_script(
        r#"
            (insert (lam x (lam y (pair x y))))
            (match (lam x (lam y (?a x y))))
        "#,
    )
    .unwrap();
    assert_eq!(
        output[1],
        "; match 1 ctx0 |-> {?a = mlam x0 x1 (pair x0 x1)}"
    );
}
#[test]
fn sexp_match_rejects_permuted_miller_parameters() {
    let error = run_sexp_script(
        r#"
            (insert (lam x (lam y (pair x y))))
            (match (lam x (lam y (?a y x))))
        "#,
    )
    .unwrap_err();
    assert_eq!(
        error,
        "line 3:13: Miller metavariable '?a' arguments are out of order; write (?a x y) on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed"
    );
}
#[test]
fn generic_binder_sugar_factors_only_independent_sum_terms() {
    let output = run_sexp_script(
        r#"
            (insert
              (@sum i (@sum j (@sum k (* (a i j) (a j k))))))
            (rewrite
              (@sum k (* (?f k) ?c))
              (* ?c (@sum k (?f k))))
            (rewrite
              (@sum k (* ?c (?f k)))
              (* ?c (@sum k (?f k))))
            (run 10)
            (guard
              (@sum i (@sum j (@sum k (* (a i j) (a j k)))))
              (@sum i (@sum j (* (a i j) (@sum k (a j k))))))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");

    let output = run_sexp_script(
        r#"
            (insert (@sum i (* (a i) (b i))))
            (match (@sum i (* ?c (?f i))))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; no matches");
}
#[test]
fn a_bare_metavariable_can_leave_a_generic_binder() {
    let output = run_sexp_script(
        r#"
            (insert (@sum i c))
            (rewrite (@sum i ?c) (* ?c (@sum i 1)))
            (run 4)
            (guard (@sum i c) (* c (@sum i 1)))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}

#[test]
fn default_extract_prefers_factored_sums_on_size_ties() {
    let output = run_sexp_script(
        r#"
            (insert (@sum x (@sum y (* 2 y))))
            (rewrite (@sum x (* ?a (?b x))) (* ?a (@sum x (?b x))))
            (rewrite (@sum x ?a) (* ?a N))
            (rewrite (* ?a ?b) (* ?b ?a))
            (run 10)
            (extract (@sum x (@sum y (* 2 y))))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "(* (sum (lam x0 x0)) (* 2 N))");
}

#[test]
fn sexp_match_extracts_the_best_equivalent_binding() {
    let output = run_sexp_script(
        r#"
            (insert (g (* a 0)))
            (rewrite (* ?x 0) 0)
            (run 4)
            (match (g ?x))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; match 1 ctx0 |-> {?x = 0}");
}
#[test]
fn sexp_match_prints_each_total_context() {
    let output = run_sexp_script(
        r#"
            (insert (f a))
            (insert 1 (f $0))
            (match (f ?x))
        "#,
    )
    .unwrap();
    assert_eq!(
        &output[2..],
        [
            "; match 1 ctx0 |-> {?x = a}",
            "; match 2 ctx1 |-> {?x = $0}"
        ]
    );
}
#[test]
fn sexp_match_miller_arguments_are_relative_to_pattern_lambdas() {
    let output = run_sexp_script(
        r#"
            (insert 1 (lam x (pair $0 x)))
            (match (lam x (pair ?top (?a x))))
        "#,
    )
    .unwrap();
    assert_eq!(output[1], "; match 1 ctx1 |-> {?top = $0, ?a = mlam x0 x0}");
}
#[test]
fn sexp_print_egraph_shows_classes_nodes_and_lifts() {
    let output = run_sexp_script("(insert 1 (lam x (pair $0 x))) (print-egraph)").unwrap();
    assert_eq!(
        output[1],
        concat!(
            "; egraph: 3 classes, 3 e-nodes\n",
            "; e0 = ctx1 |-> $0\n",
            ";   e0 <- var\n",
            "; e1 = ctx2 |-> (pair $0 $1)\n",
            ";   e1 <- (pair l_10(e0) l_01(e0))\n",
            "; e2 = ctx1 |-> (lam x0 (pair $0 x0))\n",
            ";   e2 <- (lam e1)",
        )
    );
}
#[test]
fn sexp_print_egraph_handles_an_empty_graph_and_rejects_arguments() {
    assert_eq!(
        run_sexp_script("(print-egraph)").unwrap(),
        ["; egraph: 0 classes, 0 e-nodes"]
    );
    assert_eq!(
        run_sexp_script("(print-egraph extra)").unwrap_err(),
        "line 1:1: wrong number of arguments to 'print-egraph'"
    );
}
#[test]
fn sexp_echo_emits_quoted_strings_and_atoms() {
    assert_eq!(
        run_sexp_script(r#"(echo "hello world") (echo done)"#).unwrap(),
        ["; hello world", "; done"]
    );
    assert_eq!(
        run_sexp_script("(echo)").unwrap_err(),
        "line 1:1: wrong number of arguments to 'echo'"
    );
    assert_eq!(
        run_sexp_script("(echo (not an atom))").unwrap_err(),
        "line 1:1: expected an atom"
    );
}
#[test]
fn packed_lift_limit() {
    let last = Lift::select(7, 6);
    assert_eq!(last.cod(), 7);
    assert_eq!(last.dom(), 1);
    assert!(last.get(6));
    assert_eq!(Lift::identity(7).compose(&last), last);
    assert_eq!(std::mem::size_of::<Id>(), 4);
}
#[test]
fn fat_ids_hide_identity_lifts() {
    let mut eg = EGraph::new();
    let atom = eg.atom("a", 0);
    let variable = eg.var(1, 0);
    assert_eq!(atom.show(), "e0");
    assert_eq!(variable.show(), "e1");
    assert_eq!(atom.in_context(1).unwrap().show(), "l_0(e0)");
}
#[test]
fn alpha_equivalence_and_shadowing() {
    let mut eg = EGraph::new();
    let var_x = eg.var(1, 0);
    let var_y = eg.var(1, 0);
    let id_x = eg.lam(var_x);
    let id_y = eg.lam(var_y);
    assert!(eg.equivalent(&id_x, &id_y));
    let outer_var = eg.var(2, 0);
    let inner_var = eg.var(2, 1);
    let outer_inner_lam = eg.lam(outer_var);
    let inner_inner_lam = eg.lam(inner_var);
    let outer = eg.lam(outer_inner_lam);
    let inner = eg.lam(inner_inner_lam);
    assert!(!eg.equivalent(&outer, &inner));
}
#[test]
fn free_variable_survives_binder() {
    let mut eg = EGraph::new();
    let free = eg.var(2, 0);
    let bound = eg.var(2, 1);
    let lam_free = eg.lam(free);
    let lam_bound = eg.lam(bound);
    assert_eq!(lam_free.lift().bits(), "1");
    assert_eq!(lam_bound.lift().bits(), "0");
    assert!(!eg.equivalent(&lam_free, &lam_bound));
}
#[test]
fn lift_pull_and_redundant_variable() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let z = eg.atom("0", 2);
    let xz = eg.app("*", vec![x, z]);
    let yz = eg.app("*", vec![y, z]);
    assert_eq!(xz.lift().bits(), "10");
    assert_eq!(yz.lift().bits(), "01");
    eg.union(&xz, &z);
    eg.union(&yz, &z);
    eg.rebuild();
    assert!(eg.equivalent(&xz, &yz));
    assert_eq!(eg.find(&xz).lift().bits(), "00");
}
#[test]
fn binder_rebuild_after_union() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let z = eg.atom("0", 1);
    let xz = eg.app("*", vec![x, z]);
    let lam_xz = eg.lam(xz);
    let lam_z = eg.lam(z);
    eg.union(&xz, &z);
    eg.rebuild();
    assert!(eg.equivalent(&lam_xz, &lam_z));
}
#[test]
fn ordinary_congruence_after_union() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let b = eg.atom("b", 0);
    let fa = eg.app("f", vec![a]);
    let fb = eg.app("f", vec![b]);
    assert!(!eg.equivalent(&fa, &fb));
    eg.union(&a, &b);
    eg.rebuild();
    assert!(eg.equivalent(&fa, &fb));
}
#[test]
fn match_and_rewrite_x_times_zero() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let zero = eg.atom("0", 2);
    let xz = eg.app("*", vec![x, zero]);
    let yz = eg.app("*", vec![y, zero]);
    let lhs = Pattern::app(
        "*",
        vec![Pattern::MetaVar("?x".into(), vec![]), Pattern::atom("0")],
    );
    let x_matches = eg.ematch(&lhs, &xz);
    let y_matches = eg.ematch(&lhs, &yz);
    assert_eq!(x_matches.len(), 1);
    assert_eq!(y_matches.len(), 1);
    assert!(eg.equivalent(&x_matches[0]["?x"], &x));
    assert!(eg.equivalent(&y_matches[0]["?x"], &y));
    let rule = Rewrite::new(lhs.clone(), Pattern::atom("0")).unwrap();
    assert!(eg.run(&[rule], 1).unions > 0);
    assert!(eg.equivalent(&xz, &zero));
    assert!(eg.equivalent(&yz, &zero));
    // Explicit lifted enumeration can inspect both redundant placements;
    // ordinary rewriting stays on the single canonical zero enode.
    assert_eq!(eg.ematch(&lhs, &zero).len(), 1);
    let after = eg.ematch_lifted(&lhs, &zero);
    assert!(after.iter().any(|s| eg.equivalent(&s["?x"], &x)));
    assert!(after.iter().any(|s| eg.equivalent(&s["?x"], &y)));
}
#[test]
fn run_reports_round_union_and_phase_statistics() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let zero = eg.atom("0", 0);
    let product = eg.app("*", vec![a, zero]);
    let rule = Rewrite::new(
        Pattern::app("*", vec![Pattern::meta("?x"), Pattern::atom("0")]),
        Pattern::atom("0"),
    )
    .unwrap();

    let stats = eg.run(std::slice::from_ref(&rule), 1);
    assert_eq!(stats.rounds, 1);
    assert_eq!(stats.unions, 1);
    assert_eq!(
        stats.total_time(),
        stats.match_time + stats.apply_time + stats.rebuild_time
    );
    assert!(eg.equivalent(&product, &zero));

    let stats = eg.run(&[rule], 1);
    assert_eq!(stats.rounds, 0);
    assert_eq!(stats.unions, 0);
}
#[test]
fn match_two_variables_and_repeated_variable() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let xy = eg.app("*", vec![x, y]);
    let two = Pattern::app(
        "*",
        vec![
            Pattern::MetaVar("?a".into(), vec![]),
            Pattern::MetaVar("?b".into(), vec![]),
        ],
    );
    let matches = eg.ematch(&two, &xy);
    assert_eq!(matches.len(), 1);
    assert!(eg.equivalent(&matches[0]["?a"], &x));
    assert!(eg.equivalent(&matches[0]["?b"], &y));
    let repeated = Pattern::app(
        "*",
        vec![
            Pattern::MetaVar("?a".into(), vec![]),
            Pattern::MetaVar("?a".into(), vec![]),
        ],
    );
    assert!(eg.ematch(&repeated, &xy).is_empty());
    let swapped = Pattern::app(
        "*",
        vec![
            Pattern::MetaVar("?b".into(), vec![]),
            Pattern::MetaVar("?a".into(), vec![]),
        ],
    );
    let rule = Rewrite::new(two, swapped).unwrap();
    assert!(eg.run(&[rule], 1).unions > 0);
    let yx = eg.app("*", vec![y, x]);
    assert!(eg.equivalent(&xy, &yx));
}
#[test]
fn match_inside_lambda() {
    let mut eg = EGraph::new();
    let bound = eg.var(1, 0);
    let zero = eg.atom("0", 1);
    let body = eg.app("*", vec![bound, zero]);
    let lam = eg.lam(body);
    let pat = Pattern::Lam(Box::new(Pattern::app(
        "*",
        vec![Pattern::miller("?body", vec![0]), Pattern::atom("0")],
    )));
    let matches = eg.ematch(&pat, &lam);
    assert_eq!(matches.len(), 1);
    assert!(eg.equivalent(&matches[0]["?body"], &bound));
}
#[test]
fn contextual_metavariable_crosses_an_unused_binder() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let a_under_binder = eg.atom("a", 1);
    let lam_a = eg.lam(a_under_binder);
    let term = eg.app("pair", vec![a, lam_a]);
    let pattern = Pattern::app(
        "pair",
        vec![
            Pattern::MetaVar("?x".into(), vec![]),
            Pattern::Lam(Box::new(Pattern::MetaVar("?x".into(), vec![]))),
        ],
    );

    let matches = eg.ematch(&pattern, &term);
    assert_eq!(matches.len(), 1);
    assert!(eg.equivalent(&matches[0]["?x"], &a));
}
#[test]
fn contextual_metavariable_cannot_capture_a_binder() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let bound = eg.var(1, 0);
    let lam_bound = eg.lam(bound);
    let term = eg.app("pair", vec![a, lam_bound]);
    let pattern = Pattern::app(
        "pair",
        vec![
            Pattern::MetaVar("?x".into(), vec![]),
            Pattern::Lam(Box::new(Pattern::MetaVar("?x".into(), vec![]))),
        ],
    );

    assert!(eg.ematch(&pattern, &term).is_empty());
}
#[test]
fn contextual_metavariable_can_be_inserted_under_a_binder() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let lhs = Pattern::MetaVar("?x".into(), vec![]);
    let rhs = Pattern::Lam(Box::new(Pattern::MetaVar("?x".into(), vec![])));
    let subst = eg.ematch(&lhs, &a).pop().unwrap();
    let result = eg.try_instantiate(&rhs, 0, &subst).unwrap();
    let expected_body = eg.atom("a", 1);
    let expected = eg.lam(expected_body);

    assert!(eg.equivalent(&result, &expected));
}
#[test]
fn context_extension_and_restriction_follow_dependencies() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let x_in_three = x.in_context(3).unwrap();
    assert_eq!(x_in_three.lift().bits(), "100");
    assert_eq!(x_in_three.in_context(1), Some(x));

    let newest = eg.var(3, 2);
    assert!(newest.in_context(2).is_none());

    let constant = eg.atom("c", 3);
    assert_eq!(constant.lift().bits(), "000");
    assert!(constant.in_context(0).is_some());
}
#[test]
fn redundant_binding_matches_through_an_equivalent_constant() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let zero = eg.atom("0", 1);
    let sub_xx = eg.app("sub", vec![x, x]);
    eg.union(&zero, &sub_xx);
    eg.rebuild();
    let term = eg.app("f", vec![x, zero]);
    let pattern = Pattern::app(
        "f",
        vec![
            Pattern::MetaVar("?x".into(), vec![]),
            Pattern::app(
                "sub",
                vec![
                    Pattern::MetaVar("?x".into(), vec![]),
                    Pattern::MetaVar("?x".into(), vec![]),
                ],
            ),
        ],
    );

    let matches = eg.ematch_lifted(&pattern, &term);
    assert!(!matches.is_empty());
    assert!(matches.iter().all(|s| eg.equivalent(&s["?x"], &x)));
}
#[test]
fn substitute_an_arbitrary_context_variable() {
    let mut eg = EGraph::new();
    let x = eg.var(3, 0);
    let y = eg.var(3, 1);
    let z = eg.var(3, 2);
    let body = eg.app("triple", vec![x, y, z]);
    let left = eg.var(2, 0);
    let right = eg.var(2, 1);
    let replacement = eg.app("pair", vec![left, right]);

    let result = eg.substitute(&body, 1, &replacement);
    let expected = eg.app("triple", vec![left, replacement, right]);
    assert!(eg.equivalent(&result, &expected));
}
#[test]
fn substitute_under_a_binder_without_capture() {
    let mut eg = EGraph::new();
    let outer = eg.var(2, 0);
    let inner = eg.var(2, 1);
    let body = eg.app("pair", vec![outer, inner]);
    let term = eg.lam(body);
    let replacement = eg.atom("a", 0);

    let result = eg.substitute(&term, 0, &replacement);
    let a_under_binder = eg.atom("a", 1);
    let remaining_bound = eg.var(1, 0);
    let expected_body = eg.app("pair", vec![a_under_binder, remaining_bound]);
    let expected = eg.lam(expected_body);
    assert!(eg.equivalent(&result, &expected));
}

#[test]
fn generated_substitution_agrees_with_reference_semantics() {
    // A fixed seed range gives broad, reproducible coverage while retaining
    // a small counterexample identifier when this property fails.
    for seed in 0..500_u64 {
        let target_ctx = 1 + seed as usize % 3;
        let variable = (seed as usize / 3) % target_ctx;
        let mut target_state = seed.wrapping_mul(2).wrapping_add(1);
        let mut replacement_state = seed.wrapping_mul(2).wrapping_add(2);
        let target = generated_term(target_ctx, 3, &mut target_state);
        let replacement = generated_term(target_ctx - 1, 2, &mut replacement_state);
        let expected = substitute_reference(&target, variable, &replacement, target_ctx - 1, 0);

        let mut eg = EGraph::new();
        let target_id = add_reference(&mut eg, &target, target_ctx);
        let replacement_id = add_reference(&mut eg, &replacement, target_ctx - 1);
        let expected_id = add_reference(&mut eg, &expected, target_ctx - 1);
        let actual_id = eg.substitute(&target_id, variable, &replacement_id);

        assert!(
            eg.equivalent(&actual_id, &expected_id),
            "substitution disagreed for seed {seed}, variable {variable}:\n\
             target: {target:?}\nreplacement: {replacement:?}\nexpected: {expected:?}"
        );
    }
}

#[test]
fn generated_miller_matches_reinstantiate_the_target() {
    for seed in 0..300_u64 {
        let top_ctx = seed as usize % 3;
        let mut state = seed.wrapping_add(10_000);
        let body = generated_term(top_ctx + 2, 3, &mut state);
        let mut eg = EGraph::new();
        let body = add_reference(&mut eg, &body, top_ctx + 2);
        let inner = eg.lam(body);
        let target = eg.lam(inner);
        let pattern = Pattern::Lam(Box::new(Pattern::Lam(Box::new(Pattern::miller(
            "?body",
            vec![1, 0],
        )))));

        let matches = eg.ematch(&pattern, &target);
        assert!(
            !matches.is_empty(),
            "constructed match failed for seed {seed}"
        );
        for subst in matches {
            let instantiated = eg
                .try_instantiate(&pattern, top_ctx, &subst)
                .expect("a match substitution must instantiate its own pattern");
            assert!(
                eg.equivalent(&instantiated, &target),
                "match did not reinstantiate its target for seed {seed}"
            );
        }

        // Exercise nonlinear matching as well: both occurrences must bind to
        // the same body in the same one-binder context.
        let mut state = seed.wrapping_add(20_000);
        let body = generated_term(top_ctx + 1, 2, &mut state);
        let body = add_reference(&mut eg, &body, top_ctx + 1);
        let pair = eg.app("pair", vec![body, body]);
        let target = eg.lam(pair);
        let occurrence = Pattern::miller("?item", vec![0]);
        let pattern = Pattern::Lam(Box::new(Pattern::app(
            "pair",
            vec![occurrence.clone(), occurrence],
        )));
        let matches = eg.ematch(&pattern, &target);
        assert!(
            !matches.is_empty(),
            "constructed nonlinear match failed for seed {seed}"
        );
        for subst in matches {
            let instantiated = eg
                .try_instantiate(&pattern, top_ctx, &subst)
                .expect("a nonlinear match must instantiate its own pattern");
            assert!(
                eg.equivalent(&instantiated, &target),
                "nonlinear match did not reinstantiate its target for seed {seed}"
            );
        }
    }
}
#[test]
fn substitution_prunes_the_var_times_zero_cycle() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let zero = eg.atom("0", 1);
    let x_times_zero = eg.app("*", vec![x, zero]);
    eg.union(&x_times_zero, &zero);
    eg.rebuild();
    let body = eg.app("pair", vec![x, x_times_zero]);
    let replacement = eg.atom("a", 0);

    let result = eg.substitute(&body, 0, &replacement);
    let zero_closed = eg.atom("0", 0);
    let expected = eg.app("pair", vec![replacement, zero_closed]);
    assert!(eg.equivalent(&result, &expected));
}
#[test]
fn substitution_memoizes_a_genuinely_recursive_eclass() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let fx = eg.app("f", vec![x]);
    eg.union(&x, &fx);
    eg.rebuild();
    let a = eg.atom("a", 0);

    let result = eg.substitute(&x, 0, &a);
    let fa = eg.app("f", vec![a]);
    assert!(eg.equivalent(&result, &a));
    assert!(eg.equivalent(&result, &fa));
}
#[test]
fn substitution_detects_a_cycle_lifted_through_a_binder() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let x_under_binder = x.in_context(2).unwrap();
    let lambda_x = eg.lam(x_under_binder);
    eg.union(&x, &lambda_x);
    eg.rebuild();
    let a = eg.atom("a", 0);

    let result = eg.substitute(&x, 0, &a);
    let a_under_binder = eg.atom("a", 1);
    let lambda_a = eg.lam(a_under_binder);
    assert!(eg.equivalent(&result, &a));
    assert!(eg.equivalent(&result, &lambda_a));
}
#[test]
fn extract_prefers_zero_from_the_var_times_zero_class() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let zero = eg.atom("0", 1);
    let x_times_zero = eg.app("*", vec![x, zero]);
    eg.union(&x_times_zero, &zero);

    assert_eq!(
        eg.extract(&x_times_zero),
        Some(TermCtx {
            scope: 1,
            t: Term::Atom("0".into()),
        })
    );
}
#[test]
fn extract_skips_a_recursive_enode() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let fa = eg.app("f", vec![a]);
    eg.union(&a, &fa);

    assert_eq!(
        eg.extract(&a),
        Some(TermCtx {
            scope: 0,
            t: Term::Atom("a".into()),
        })
    );
}
#[test]
fn extract_reconstructs_variable_placements_under_binders() {
    let mut eg = EGraph::new();
    let outer = eg.var(2, 0);
    let inner = eg.var(2, 1);
    let pair = eg.app("pair", vec![outer, inner]);
    let term = eg.lam(pair);

    assert_eq!(
        eg.extract(&term),
        Some(TermCtx {
            scope: 1,
            t: Term::Lam(Box::new(Term::App(
                "pair".into(),
                vec![Term::FVar(0.into()), Term::BVar(0.into())],
            ))),
        })
    );
}
#[test]
fn extract_accepts_a_custom_monotone_cost() {
    fn weighted_size(term: &Term) -> usize {
        match term {
            Term::FVar(_) | Term::BVar(_) => 1,
            Term::Atom(name) if name.as_str() == "expensive" => 100,
            Term::Atom(_) => 1,
            Term::App(_, children) => 1 + children.iter().map(weighted_size).sum::<usize>(),
            Term::Lam(body) => 1 + weighted_size(body),
        }
    }

    let mut eg = EGraph::new();
    let expensive = eg.atom("expensive", 0);
    let cheap = eg.atom("cheap", 0);
    let wrapped = eg.app("wrap", vec![cheap]);
    eg.union(&expensive, &wrapped);

    assert_eq!(
        eg.extract_with(&expensive, weighted_size)
            .unwrap()
            .to_string(),
        "(wrap cheap)"
    );
}

#[test]
fn default_extract_tie_breaks_by_binders_then_depth() {
    let mut eg = EGraph::new();

    let under_binder = eg.atom("a", 1);
    let binder = eg.lam(under_binder);
    let a = eg.atom("a", 0);
    let no_binder = eg.app("f", vec![a]);
    eg.union(&binder, &no_binder);
    assert_eq!(eg.extract(&binder).unwrap().to_string(), "(f a)");

    let b = eg.atom("b", 0);
    let deep = eg.app("g", vec![no_binder]);
    let shallow = eg.app("h", vec![a, b]);
    eg.union(&deep, &shallow);
    assert_eq!(eg.extract(&deep).unwrap().to_string(), "(h a b)");
}
#[test]
fn beta_avoids_capture_when_the_argument_is_free() {
    let mut eg = EGraph::new();
    // In y |- (λx. λy'. x) y, the argument y must remain the outer
    // context variable rather than becoming captured by y'.
    let outer_x = eg.var(3, 1);
    let inner_lambda = eg.lam(outer_x);
    let function = eg.lam(inner_lambda);
    let free_y = eg.var(1, 0);
    let redex = eg.app("app", vec![function, free_y]);

    eg.saturate(&[beta_rule()]);
    assert_eq!(eg.extract(&redex).unwrap().to_string(), "(lam $0)");
    let expected_free_y = eg.var(2, 0);
    let expected = eg.lam(expected_free_y);
    assert!(eg.equivalent(&redex, &expected));
    let captured_y = eg.var(2, 1);
    let incorrect = eg.lam(captured_y);
    assert!(!eg.equivalent(&redex, &incorrect));
}
#[test]
fn beta_does_not_shift_a_lambda_argument() {
    let mut eg = EGraph::new();
    // Slotted's t_shift regression: (λx. λy. x) (λz. z).
    let outer_x = eg.var(2, 0);
    let inner_lambda = eg.lam(outer_x);
    let function = eg.lam(inner_lambda);
    let z = eg.var(1, 0);
    let identity = eg.lam(z);
    let redex = eg.app("app", vec![function, identity]);

    eg.saturate(&[beta_rule()]);
    assert_eq!(eg.extract(&redex).unwrap().to_string(), "(lam (lam #0))");
    let expected_z = eg.var(2, 1);
    let expected_identity = eg.lam(expected_z);
    let expected = eg.lam(expected_identity);
    assert!(eg.equivalent(&redex, &expected));
}
#[test]
fn beta_discards_an_omega_argument_and_terminates() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 1);
    let constant_function = eg.lam(a);
    let omega_var = eg.var(1, 0);
    let omega_body = eg.app("app", vec![omega_var, omega_var]);
    let delta = eg.lam(omega_body);
    let omega = eg.app("app", vec![delta, delta]);
    let redex = eg.app("app", vec![constant_function, omega]);

    eg.saturate(&[beta_rule()]);
    assert_eq!(
        eg.extract(&redex),
        Some(TermCtx {
            scope: 0,
            t: Term::Atom("a".into()),
        })
    );
}
#[test]
fn beta_handles_the_alpha_shared_self_recursive_class() {
    let mut eg = EGraph::new();
    // λx. (λy. y) x reduces to λx. x. With alpha sharing, the class can
    // also contain a representation that refers back to itself.
    let inner_y = eg.var(2, 1);
    let inner_identity = eg.lam(inner_y);
    let outer_x = eg.var(1, 0);
    let body = eg.app("app", vec![inner_identity, outer_x]);
    let term = eg.lam(body);

    eg.saturate(&[beta_rule()]);
    assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam #0)");
    let expected_x = eg.var(1, 0);
    let expected = eg.lam(expected_x);
    assert!(eg.equivalent(&term, &expected));
}
#[test]
fn beta_reduces_multiple_steps_after_self_application() {
    let mut eg = EGraph::new();
    // (λx. x x) (λy. y) -> (λy. y) (λy. y) -> λy. y.
    let x = eg.var(1, 0);
    let xx = eg.app("app", vec![x, x]);
    let duplicator = eg.lam(xx);
    let y = eg.var(1, 0);
    let identity = eg.lam(y);
    let term = eg.app("app", vec![duplicator, identity]);

    eg.saturate(&[beta_rule()]);
    assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam #0)");
    assert!(eg.equivalent(&term, &identity));
}
#[test]
fn egg_simple_tests() {
    let rules = egg_simple_rules();

    let mut eg = EGraph::new();
    let zero = eg.atom("0", 0);
    let forty_two = eg.atom("42", 0);
    let term = eg.app("*", vec![zero, forty_two]);
    eg.saturate(&rules);
    assert_eq!(
        eg.extract(&term),
        Some(TermCtx {
            scope: 0,
            t: Term::Atom("0".into()),
        })
    );

    let mut eg = EGraph::new();
    let zero = eg.atom("0", 0);
    let one = eg.atom("1", 0);
    let foo = eg.atom("foo", 0);
    let product = eg.app("*", vec![one, foo]);
    let term = eg.app("+", vec![zero, product]);
    eg.saturate(&rules);
    assert_eq!(
        eg.extract(&term),
        Some(TermCtx {
            scope: 0,
            t: Term::Atom("foo".into()),
        })
    );
}
#[test]
fn egg_math_associate_adds() {
    let mut eg = EGraph::new();
    let atoms: Vec<_> = (1..=7).map(|n| eg.atom(&n.to_string(), 0)).collect();
    let mut input = atoms[6];
    for atom in atoms[..6].iter().rev() {
        input = eg.app("+", vec![*atom, input]);
    }
    let var = Pattern::meta;
    let plus = |left, right| Pattern::app("+", vec![left, right]);
    let rewrite = |lhs, rhs| Rewrite::new(lhs, rhs).unwrap();
    let rules = [
        rewrite(plus(var("?a"), var("?b")), plus(var("?b"), var("?a"))),
        rewrite(
            plus(var("?a"), plus(var("?b"), var("?c"))),
            plus(plus(var("?a"), var("?b")), var("?c")),
        ),
    ];

    eg.saturate(&rules);
    assert_eq!(eg.class_count(), 127);
    assert_eq!(eg.node_count(), 1939);
    let mut goal = atoms[0];
    for atom in atoms[1..].iter() {
        goal = eg.app("+", vec![*atom, goal]);
    }
    assert!(eg.equivalent(&input, &goal));
}
#[test]
fn egg_lambda_under() {
    let mut eg = EGraph::new();
    let four = eg.atom("4", 1);
    let inner_y = eg.var(2, 1);
    let inner_identity = eg.lam(inner_y);
    let inner_redex = eg.app("app", vec![inner_identity, four]);
    let sum = eg.app("+", vec![four, inner_redex]);
    let term = eg.lam(sum);

    eg.saturate(&[beta_rule()]);
    let fold_four_plus_four = [Rewrite::new(
        Pattern::app("+", vec![Pattern::atom("4"), Pattern::atom("4")]),
        Pattern::atom("8"),
    )
    .unwrap()];
    eg.saturate(&fold_four_plus_four);
    assert_eq!(eg.extract(&term).unwrap().to_string(), "(lam 8)");
}
#[test]
fn egg_lambda_compose_beta_core() {
    let mut eg = EGraph::new();
    let f = eg.var(3, 0);
    let g = eg.var(3, 1);
    let x = eg.var(3, 2);
    let gx = eg.app("app", vec![g, x]);
    let fgx = eg.app("app", vec![f, gx]);
    let compose_x = eg.lam(fgx);
    let compose_g = eg.lam(compose_x);
    let compose = eg.lam(compose_g);

    let y = eg.var(1, 0);
    let one = eg.atom("1", 1);
    let add_one_body = eg.app("+", vec![y, one]);
    let add_one = eg.lam(add_one_body);
    let partial = eg.app("app", vec![compose, add_one]);
    let twice = eg.app("app", vec![partial, add_one]);

    eg.saturate(&[beta_rule()]);
    assert_eq!(
        eg.extract(&twice).unwrap().to_string(),
        "(lam (+ (+ #0 1) 1))"
    );
}
#[test]
fn identical_binders_in_sibling_lambdas_match_one_metavariable() {
    let mut eg = EGraph::new();
    let left_bound = eg.var(1, 0);
    let right_bound = eg.var(1, 0);
    let left = eg.lam(left_bound);
    let right = eg.lam(right_bound);
    let term = eg.app("pair", vec![left, right]);
    let pattern = Pattern::app(
        "pair",
        vec![
            Pattern::Lam(Box::new(Pattern::miller("?body", vec![0]))),
            Pattern::Lam(Box::new(Pattern::miller("?body", vec![0]))),
        ],
    );

    assert_eq!(eg.ematch(&pattern, &term).len(), 1);
}
#[test]
fn enumerate_alternative_enodes_in_one_class() {
    let mut eg = EGraph::new();
    let a = eg.atom("a", 0);
    let b = eg.atom("b", 0);
    let aa = eg.app("f", vec![a, a]);
    let bb = eg.app("f", vec![b, b]);
    eg.union(&aa, &bb);
    eg.rebuild();
    let repeated = Pattern::app(
        "f",
        vec![
            Pattern::MetaVar("?v".into(), vec![]),
            Pattern::MetaVar("?v".into(), vec![]),
        ],
    );
    let matches = eg.ematch(&repeated, &aa);
    assert_eq!(matches.len(), 2);
    assert!(matches.iter().any(|s| eg.equivalent(&s["?v"], &a)));
    assert!(matches.iter().any(|s| eg.equivalent(&s["?v"], &b)));
}
#[test]
fn equating_two_placements_of_one_raw_id_uses_the_equalizer() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let fx = eg.app("f", vec![x]);
    let fy = eg.app("f", vec![y]);

    assert_eq!(fx.raw(), fy.raw());
    assert!(eg.union(&fx, &fy));
    eg.rebuild();
    assert!(eg.equivalent(&fx, &fy));
    assert_eq!(eg.find(&fx).lift().bits(), "00");
}
#[test]
fn rebuild_reports_a_count_neutral_canonical_change() {
    let mut eg = EGraph::new();
    let x = eg.var(1, 0);
    let zero = eg.atom("0", 1);
    let _fx = eg.app("f", vec![x]);
    eg.union(&x, &zero);
    let classes_before = eg.class_count();

    assert!(eg.rebuild());
    assert_eq!(eg.class_count(), classes_before);
}
#[test]
fn concrete_context_variables_in_patterns_respect_binders() {
    let output = run_sexp_script(
        "(insert (lam x (f x))) (rewrite (lam x (f x)) (lam x x)) (run 4) (extract (lam x (f x)))",
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "(lam x0 x0)");
}
#[test]
fn miller_metavariable_must_name_a_captured_binder() {
    let mut eg = EGraph::new();
    let bound = eg.var(1, 0);
    let term = eg.lam(bound);
    let bare = sexp_pattern(&parse_sexps("(lam x ?a)").unwrap()[0]).unwrap();
    let allowed = sexp_pattern(&parse_sexps("(lam x (?a x))").unwrap()[0]).unwrap();

    assert!(eg.ematch(&bare, &term).is_empty());
    let matches = eg.ematch(&allowed, &term);
    assert_eq!(matches.len(), 1);
    assert!(eg.equivalent(&matches[0]["?a"], &bound));
}
#[test]
fn sexp_frontend_uses_miller_binder_lists() {
    let output = run_sexp_script(
        r#"
            (insert (lam x x))
            (rewrite (lam x ?a) misses)
            (rewrite (lam x (?a x)) matches)
            (run 4)
            (extract (lam x x))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "matches");
}
#[test]
fn miller_metavariable_implicitly_keeps_the_top_scope() {
    let mut eg = EGraph::new();
    let outer = eg.var(1, 0);
    let outer_under_binder = outer.in_context(2).unwrap();
    let term = eg.lam(outer_under_binder);
    let pattern = sexp_pattern(&parse_sexps("(lam x ?a)").unwrap()[0]).unwrap();

    let matches = eg.ematch(&pattern, &term);
    assert_eq!(matches.len(), 1);
    assert!(eg.equivalent(&matches[0]["?a"], &outer));
}
#[test]
fn miller_arguments_can_select_a_later_nested_binder() {
    let mut eg = EGraph::new();
    let inner = eg.var(2, 1);
    let inner_lambda = eg.lam(inner);
    let term = eg.lam(inner_lambda);
    let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?f y)))").unwrap()[0]).unwrap();

    let subst = eg.ematch(&pattern, &term).pop().unwrap();
    let rebuilt = eg.try_instantiate(&pattern, 0, &subst).unwrap();
    assert!(eg.equivalent(&rebuilt, &term));
}
#[test]
fn miller_indices_count_outward_from_the_nearest_pattern_binder() {
    let mut eg = EGraph::new();
    let outer = eg.var(2, 0);
    let inner_lambda = eg.lam(outer);
    let term = eg.lam(inner_lambda);
    let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?f x)))").unwrap()[0]).unwrap();

    let subst = eg.ematch(&pattern, &term).pop().unwrap();
    let rebuilt = eg.try_instantiate(&pattern, 0, &subst).unwrap();
    assert!(eg.equivalent(&rebuilt, &term));
}
#[test]
fn miller_arguments_must_be_distinct_bound_variables() {
    assert!(
        sexp_match_pattern(&parse_sexps("(lam x (?a x x))").unwrap()[0])
            .unwrap_err()
            .contains("repeats")
    );
    let mut eg = EGraph::new();
    let bound = eg.var(1, 0);
    let _term = eg.lam(bound);
    assert!(
        sexp_match_pattern(&parse_sexps("(lam x (?a y))").unwrap()[0])
            .unwrap_err()
            .contains("may only be applied to bound variables")
    );
}
#[test]
fn miller_rhs_application_substitutes_arbitrary_terms() {
    let output = run_sexp_script(
        r#"
            (insert (lam x x))
            (rewrite (lam x (?a x)) (?a (foo biz)))
            (run 4)
            (guard (lam x x) (foo biz))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}
#[test]
fn miller_rhs_application_can_permute_parameters() {
    let output = run_sexp_script(
        r#"
            (insert (lam x (lam y (pair x y))))
            (rewrite
                (lam x (lam y (?a x y)))
                (lam x (lam y (?a y x))))
            (run 4)
            (guard
                (lam x (lam y (pair x y)))
                (lam x (lam y (pair y x))))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}
#[test]
fn permuted_lhs_arguments_are_rejected() {
    let error =
        run_sexp_script("(rewrite (lam x (lam y (?a y x))) (lam x (lam y (?a x y))))").unwrap_err();
    assert!(error.contains("write (?a x y)"));
    assert!(error.contains("permute its arguments on the rewrite right-hand side"));
}
#[test]
fn miller_matching_is_read_only() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let pair = eg.app("pair", vec![x, y]);
    let inner = eg.lam(pair);
    let term = eg.lam(inner);
    let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?a x y)))").unwrap()[0]).unwrap();
    let nodes = eg.node_count();
    let ids = eg.raw_id_count();

    let subst = eg.ematch(&pattern, &term).pop().unwrap();

    assert_eq!(eg.node_count(), nodes);
    assert_eq!(eg.raw_id_count(), ids);
    assert_eq!(subst["?a"].ctx(), 2);
    assert_eq!(subst["?a"].lift().bits(), "11");
}
#[test]
fn miller_permutation_preserves_the_implicit_top_context() {
    let output = run_sexp_script(
        r#"
            (insert 1 (lam x (lam y (triple $0 x y))))
            (rewrite
                (lam x (lam y (?a x y)))
                (lam x (lam y (?a y x))))
            (run 4)
            (guard 1
                (lam x (lam y (triple $0 x y)))
                (lam x (lam y (triple $0 y x))))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");
}
#[test]
fn miller_rhs_application_ignores_dropped_parameters() {
    let output = run_sexp_script(
        r#"
            (insert (lam x (lam y x)))
            (rewrite
                (lam x (lam y (?a x y)))
                (lam x (lam y (?a y x))))
            (run 4)
            (guard (lam x (lam y x)) (lam x (lam y y)))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "; guard passed");

    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let inner = eg.lam(x);
    let term = eg.lam(inner);
    let pattern = sexp_pattern(&parse_sexps("(lam x (lam y (?a x y)))").unwrap()[0]).unwrap();
    let subst = eg.ematch(&pattern, &term).pop().unwrap();
    assert_eq!(subst["?a"].ctx(), 2);
    assert_eq!(subst["?a"].lift().bits(), "10");
}
#[test]
fn out_of_order_miller_pattern_is_rejected_statically() {
    let error = run_sexp_script(
        r#"
            (insert (lam x (lam y (pair (f x y) (f y x)))))
            (match (lam x (lam y (pair (?a x y) (?a y x)))))
        "#,
    )
    .unwrap_err();
    assert!(error.contains("write (?a x y)"));

    let rewrite_error =
        run_sexp_script("(rewrite (lam x (lam y (pair (?a x y) (?a y x)))) ok)").unwrap_err();
    assert!(rewrite_error.contains("write (?a x y)"));
}
#[test]
fn nonlinear_miller_occurrences_with_the_same_order_are_allowed() {
    let pattern =
        sexp_pattern(&parse_sexps("(lam x (lam y (lam z (pair (?a x y) (?a y z)))))").unwrap()[0])
            .unwrap();
    pattern.validate_match_pattern().unwrap();
}
#[test]
fn nonlinear_miller_matching_moves_bindings_between_local_contexts() {
    let output = run_sexp_script(
        r#"
            (insert
                (lam x (lam y (lam z
                    (pair (f x y) (f y z))))))
            (match
                (lam x (lam y (lam z
                    (pair (?a x y) (?a y z))))))
        "#,
    )
    .unwrap();
    assert!(output[1].starts_with("; match 1 ctx0 |->"));
}
#[test]
fn nonlinear_miller_matching_rejects_different_bodies() {
    let output = run_sexp_script(
        r#"
            (insert
                (lam x (lam y (lam z
                    (pair (f x y) (g y z))))))
            (match
                (lam x (lam y (lam z
                    (pair (?a x y) (?a y z))))))
        "#,
    )
    .unwrap();
    assert_eq!(output[1], "; no matches");
}
#[test]
fn nonlinear_miller_occurrences_must_have_consistent_arity() {
    let pattern =
        sexp_pattern(&parse_sexps("(lam x (lam y (pair (?a x) (?a x y))))").unwrap()[0]).unwrap();
    assert!(
        pattern
            .validate_match_pattern()
            .unwrap_err()
            .contains("inconsistent arity")
    );
}
#[test]
fn rewrites_are_validated_before_running() {
    let error = run_sexp_script("(rewrite (#subst $0 $0 fred) fred)").unwrap_err();
    assert!(error.contains("#subst is only allowed on a rewrite right-hand side"));

    let error = run_sexp_script("(rewrite ?x ?y)").unwrap_err();
    assert!(error.contains("unbound metavariable '?y'"));

    let error = run_sexp_script("(rewrite (lam x (?a x)) (lam x ?a))").unwrap_err();
    assert!(error.contains("has arity 1 on the left and 0 on the right"));
}
#[test]
fn miller_permutation_memoizes_recursive_eclasses() {
    let mut eg = EGraph::new();
    let x = eg.var(2, 0);
    let y = eg.var(2, 1);
    let pair = eg.app("pair", vec![x, y]);
    let recursive = eg.app("f", vec![pair]);
    eg.union(&pair, &recursive);
    eg.rebuild();

    let inner = eg.lam(pair);
    let term = eg.lam(inner);
    let lhs = sexp_pattern(&parse_sexps("(lam x (lam y (?a x y)))").unwrap()[0]).unwrap();
    let rhs = sexp_pattern(&parse_sexps("(lam x (lam y (?a y x)))").unwrap()[0]).unwrap();
    let rule = Rewrite::new(lhs, rhs).unwrap();
    assert!(eg.run(&[rule], 1).unions > 0);

    let swapped = eg.app("pair", vec![y, x]);
    let inner = eg.lam(swapped);
    let expected = eg.lam(inner);
    assert!(eg.equivalent(&term, &expected));
}
#[test]
fn sexp_subst_builtin_is_available_on_rewrite_right_hand_sides() {
    let output = run_sexp_script(
        r#"
            (insert 1 (app (lam x x) $0))
            (rewrite (app (lam x (?body x)) ?arg) (#subst (?body x) x ?arg))
            (run 6)
            (extract 1 (app (lam x x) $0))
        "#,
    )
    .unwrap();
    assert_eq!(output.last().unwrap(), "$0");
}
#[test]
fn printed_quoted_atoms_round_trip() {
    let mut eg = EGraph::new();
    let id = add_sexp_term(&mut eg, &parse_sexps("\"a b\"").unwrap()[0], 0).unwrap();
    let printed = eg.extract(&id).unwrap().to_string();
    assert_eq!(printed, "\"a b\"");
    let reparsed = add_sexp_term(&mut eg, &parse_sexps(&printed).unwrap()[0], 0).unwrap();
    assert!(eg.equivalent(&id, &reparsed));
}
#[test]
fn overly_deep_frontend_context_is_an_error() {
    assert!(
        run_sexp_script("(insert 8 a)")
            .unwrap_err()
            .contains("at most 7")
    );
}
