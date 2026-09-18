# Lambda MicroEgg

Using Lifting e-graph ideas https://arxiv.org/abs/2606.22734  https://www.youtube.com/watch?v=h1CzZguA6DE

The basic idea is [slotted e-graphs](https://dl.acm.org/doi/10.1145/3729326) combined with Mcbride's [Everybody's Got to Be Somewhere](https://arxiv.org/abs/1807.04085).

The starting point of the basic e-graph implementation is Max Willsey's microegg https://github.com/mwillsey/microegg

WASM Demo pages : <www.philipzucker.com/lambda-microegg>

The "lambda" supported here isn't really a lambda (in the sense that the focus of the thing is to beta substitution). It's a binder. The point of it is alpha equivalence and well-scoping. But I do also have a built in substitution operator for the right hand side of rules.

Another important concept is that of a Miller pattern.
<https://www.philipzucker.com/ho_unify/>
https://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/proghol/extract.html Chapter 4

 `(lam x (lam y (?a x)))` is a Miller pattern because the higher order pattern variable `?a` is applied to distinct bound variable. It will match `(lam x (lam y x))` but fail to match `(lam x (lam y y))` because `?a` can't capture the `y`.  
 
 `(lam x (?a (+ one x)))` would _not_ be a Miller pattern, and is not supported. 
 
 Miller patterns are basically the least reasonable thing you can do to have bound variables but reaspect scope. They are intrinsically tractable to implement, whereas full higher order matching even outside of the e-graph can encode undecidable problems.


# Running

```sh
cargo run --release -- example.sexp
```

# Commands

- `insert`
- `union`
- `rewrite`
- `run`
- `match`
- `guard`
- `echo`
- `reset`
- `print-egraph`

Binder operators use `(@OP NAME BODY)` syntax. For example,
`(@sum i (f i))` is macro expanded as `(sum (lam i (f i)))`.


# AI disclosure

I am disturbed and depressed by AI. The code in this codebase was produced by giving Max's microegg, my thinning egraph implementation, blog posts and paper to an agent. It required a lot of back and forth.