# Proof generation plan

Proof data should be parallel to the operational e-graph data rather than part of `Id`.
`Id` already carries a lift, and proof tracking should be removable without changing its size or the
hot paths that pass it around.

The implementation starts with `ProofUnionFind` in `src/proof.rs`. Its ordinary data is a parent
array and a name memo. With proofs enabled, an optional state adds three parallel structures:

- an arena of typed proof constructors (`Refl`, `Symm`, `Trans`, and external assumptions);
- one proof ID per parent edge;
- one proof ID per memo entry, relating the external term to its allocated e-class name.

No constructor contains rendered Lean text. Rendering happens once, when `lean_proof` emits term
and proof `let` bindings. The generated theorem is checked by Lean in the test suite when `lean` is
available.

The next stage is the context-zero fragment of `EGraph`: atoms and binary applications, without
variables, binders, or non-identity lifts. Each raw e-class will retain its immutable defining node.
Rebuild can then justify canonicalizing an application with `congrArg₂`, and a memo collision can
join two definitions by transitivity. Rewrite applications initially become explicit theorem
assumptions; instantiating named rewrite theorems can be added after congruence works.

## Lifts

An `n`-argument term can be interpreted as a function of its context. A lift is precomposition with
the projection that selects the used arguments. If `p : f = g`, equality of two lifted terms follows
from `congrArg` applied to that precomposition function (or, pointwise, repeated `funext`). This is
the straightforward direction.

Dependency shrinking is an existential factorization. Suppose `Γ` is the common context, `X` and
`Y` are the variables private to the two sides, and

```lean
h : (fun γ x (_ : Y) ↦ e γ x) = fun γ (_ : X) y ↦ e₂ γ y
```

The general constructive requirement is a pair of filler substitutions `fillX : (γ : Γ) → X γ`
and `fillY : (γ : Γ) → Y γ`. A closed default supplies a constant filler. Duplicating a retained
variable supplies a filler by projecting that variable out of `γ`. Any computed term in the retained
context can serve as a filler in the same way. Choose `e₃ γ := e γ (fillX γ)`; `h` shows that every
choice of the private variables has this value.

When `X` and `Y` are inhabited nondependent types, their defaults give these fillers automatically.
`proofs/DependencyPruning.lean` checks both the general filler theorem and this specialization in
Lean. It also checks an `Empty` counterexample showing that there is no unrestricted rule.

The inhabitance condition matters for ordinary function semantics: equality over an empty private
context is vacuous and need not exhibit a value in `A`. For a single-sorted object language, one
`Inhabited` instance for its semantic carrier is enough. With typed binders, every discarded
variable type needs a witness, or the certificate must carry a syntactic support judgment instead.

The chosen `e₃` also need not be representable by a source-language term. That is compatible with
the current e-graph, whose fresh dependency-pruned class may have no extractable enode. It can still
exist as an internal Lean `let` binding used only by the certificate.

## Factored rewrite rules

A proof-producing rewrite can carry the factorization instead of asking ordinary equality to recover
it. Its logical interface is a span through a mediator in a smaller context:

```text
                 core : Term Δ
                 /           \
          left proof       right proof
               /               \
       lhs : Term Γ₁       rhs : Term Γ₂
```

Here `Δ` embeds into both `Γ₁` and `Γ₂`; it may be smaller than their exact intersection. In Lean,
the rule assumption has the shape

```lean
Σ core : Term Δ, lift left core = lhs × lift right core = rhs
```

or an equivalent structure with named fields. Applying the rule instantiates `core` as well as both
proof legs. The resulting core ID is the witness used when union creates a dependency-pruned class.
This is strictly richer than an assumption `lhs = rhs` and is constructively eliminable.

The runtime can offer ordinary and factored rules. With proof tracking disabled, a factored rule
erases to its left and right patterns. With proof tracking enabled, an ordinary rule is sufficient
as long as its application does not reduce support; an application that needs a fresh common class
must provide a factorization or return a proof-generation error. Making every proof-producing rule
factored would give a simpler invariant at the cost of a more demanding user interface.

The proof arena should store the instantiated span rather than folding it immediately into a plain
equality. Keeping the mediator makes later equalizer and pullback operations compositional and lets
final Lean printing destructure the rule witness only when it is actually used.
