# Lambda MicroEgg

Using Lifting e-graph ideas https://arxiv.org/abs/2606.22734  https://www.youtube.com/watch?v=h1CzZguA6DE

The basic idea is slotted e-graphs combined with Mcbride's Everybody's Got to Be Somewhere.

The starting point of the basic e-graph implementation is Max Willsey's microegg https://github.com/mwillsey/microegg

WASM Demo pages : <www.philipzucker.com/lambda-microegg>

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
`(@sum i (f i))` is represented internally as `(sum (lam i (f i)))`.
