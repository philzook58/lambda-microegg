# Lambda MicroEgg

Using Lifting e-graph ideas https://arxiv.org/abs/2606.22734  https://www.youtube.com/watch?v=h1CzZguA6DE

Blog posts:
    - <https://www.philipzucker.com/lambda_miller_egg/>

The basic idea is [slotted e-graphs](https://dl.acm.org/doi/10.1145/3729326) combined with Mcbride's [Everybody's Got to Be Somewhere](https://arxiv.org/abs/1807.04085).

The starting point of the basic e-graph implementation is Max Willsey's microegg https://github.com/mwillsey/microegg

WASM Demo pages : <www.philipzucker.com/lambda-microegg>

Binders are generic. `(@sum i BODY)` and `(@lam x BODY)` have the same internal
shape, `Binder(Symbol, Id)`; `lam` is only the conventional symbol used when
modeling lambda calculus. Binder nodes provide alpha equivalence and
well-scoping, and `#subst` supplies explicit substitution on rewrite right-hand
sides.

Another important concept is that of a Miller pattern.
<https://www.philipzucker.com/ho_unify/>
https://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/proghol/extract.html Chapter 4

 `(@lam x (@lam y {?a x}))` is a Miller pattern because the higher order pattern variable `?a` is applied to distinct bound variable. It will match `(@lam x (@lam y x))` but fail to match `(@lam x (@lam y y))` because `?a` can't capture the `y`.
 
 `(@lam x {?a (+ one x)})` would _not_ be a Miller pattern, and is not supported.
 
 Miller patterns are basically the reasonable least thing you can do to have bound variables but reaspect scope. They are intrinsically tractable to implement, whereas full higher order matching even outside of the e-graph can encode undecidable problems.

There is an instrinsic question about how to take patterns that are bound in a different context than the root of the pattern, carry them up to the root, and carry them over to the right hand side of the pattern. Miller patterns are a reasonable language for describing how you want this done. You have to eta expand them on the right hand side or else you don't really know


# Running

```sh
cargo run --release -- example.sexp
```

# Commands

- `insert`
- `union`
- `rewrite`
- `birewrite` — adds both directions of a rule, so both sides must be valid
  match patterns binding the same metavariables
- `run`
- `match`
- `guard`
- `extract`
- `echo`
- `fail`
- `reset`
- `print-egraph`

Binder operators use `(@OP NAME BODY)` syntax. For example,
`(@sum i (f i))` is stored directly as the `sum` binder. Lambda calculus uses
the same generic binder representation through `@lam`.

Square brackets are curried higher-order application: `[f x y]` is stored as
`HOApp(HOApp(f, x), y)`. Parenthesized `(f x y)` remains a single n-ary,
first-order application node. Braces denote a metavariable occurrence rather
than an e-node. On a match left-hand side its arguments are Miller parameters;
on the right they instantiate the captured body. Beta reduction can be written
`[(@lam x {?body x}) ?e]` to `{?body ?e}`.


# AI disclosure

The code in this codebase was initially produced by giving Max's microegg, my thinning egraph implementations, blog posts and paper to an agent.
