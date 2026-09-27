# Proof generation plan

Proof data should be parallel to the operational e-graph data rather than part of `Id`.
`Id` already carries a lift, and proof tracking should be removable without changing its size or the
hot paths that pass it around.

The implementation starts with `ProofUnionFind` in `src/proof.rs`. Its ordinary data is a
size-balanced, path-compressed parent array and a name memo. With proofs enabled, an optional state
adds a second, uncompressed explanation forest in the style of
[Nieuwenhuis and Oliveras](https://www.cs.upc.edu/~oliveras/rta05.pdf):

- an arena of typed proof constructors (`Refl`, `Symm`, `Trans`, and external assumptions);
- a proof parent and an atomic union reason per explanation-forest edge;
- one proof ID per memo entry, relating the external term to its allocated e-class name.

Successful unions reroot the smaller component's explanation tree at the union endpoint and connect
it to the other endpoint. Rerooting flips edge directions without allocating proof terms. Ordinary
`find` can therefore compress paths freely without changing explanations. At print time, the unique
path between the requested terms selects the nonredundant union assumptions before dead-code
traversal selects the proof-arena nodes. No constructor contains rendered Lean text. Rendering
happens once, when `lean_proof` emits term and proof `let` bindings. The generated theorem is checked
by Lean in the test suite when `lean` is available.

For a fixed pseudorandom spanning tree, asking for `x0 = x(n-1)` gives the following standalone
certificate sizes. “Eager” is the earlier design that stored composed proofs on compressed
union-find parent edges; “double” is the separate explanation forest.

| Nodes | Eager arena | Double arena | Eager assumptions | Double assumptions | Eager bytes | Double bytes |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 46 | 22 | 4 | 1 | 1,010 | 363 |
| 20 | 93 | 49 | 11 | 5 | 2,120 | 1,040 |
| 30 | 138 | 65 | 16 | 4 | 3,192 | 844 |

`examples/proof_union_find_random.rs` reproduces the workload. The checked three-, four-, and
five-node certificates are kept in `proofs/UnionFindRandom{3,4,5}.lean` so the selected paths are
easy to inspect.

The context-zero fragment is now integrated into `EGraph`: atoms and binary applications, without
variables, binders, or non-identity lifts. `EGraph::new_with_proofs` allocates parallel proof state;
ordinary `EGraph::new` pays no proof-arena cost. Each raw e-class retains its immutable defining
node. The e-graph uses the same separation as the standalone union-find: operational parent links
are compressed freely, while a size-balanced proof forest retains one reason for each successful
union. `EGraph::lean_proof` selects the unique forest path and prints only live term and proof
bindings, preserving their arena IDs rather than densely renumbering them.

Application memo collisions are lazy proof-forest reasons. They retain the corresponding function
and argument pairs rather than constructing their proofs. Those pairs were already connected before
the congruence edge was inserted; because every later successful union only connects two trees,
their unique paths can never acquire that edge. Recursive explanation is therefore acyclic without
capturing eager child proofs. A congruence proof and its child proofs enter the term arena only if
final path selection reaches that reason. `examples/proof_egraph.rs` demonstrates `a = b` producing
`f a = f b`, and the test suite checks both the delayed allocation and the resulting certificate
with Lean.

Application congruence uses the direct core Lean combinator for each shape: `congrArg` when only the
argument changes, `congrFun` when only the function changes, and `congr` when both
change. Generated Lean uses native function application, so the certificate context gives symbols
their actual function types instead of supplying an untyped `app` symbol. This also makes Lean reject
any certificate in which the otherwise-untyped e-graph has combined applications inconsistently.

Unnamed rewrite applications become explicit theorem assumptions. Operations involving variables,
binders, dependency shrinking, or non-identity lifts record a precise unsupported-operation error
for final printing.

Context-zero rewrites may instead be constructed with `Rewrite::named`. In proof mode, the apply
phase first builds the operational RHS and checks that it would create a new union. Only then does
it normalize both instantiated sides and allocate a compact `Rewrite(name, substitutions)` proof
node. The Lean printer applies the named rule and uses the already-recorded parent equalities to
normalize it to the union endpoints. A failed RHS, unsupported normalization, or already-equal pair
allocates no rewrite proof and performs no proof-producing union.

When the stored endpoint definitions are exactly the instantiated rule sides, the rewrite node uses
those raw endpoints directly and lets Lean unfold their local `let` bindings. If prior unions have
made an equivalent but differently defined term the representative, the printer retains the explicit
normalization path. This removes all synthetic normalization from the `(x + 0) + 0` example while
remaining valid for later AC saturation rounds.

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

## First-order scaling checkpoint

The named first-order AC examples use explicit rule, congruence, symmetry, and transitivity proof
objects. AC3 checks in about 0.32 seconds, AC4 in 0.95 seconds, and AC5 in 6.95 seconds on the same
machine; an empty Lean invocation takes about 0.22 seconds. AC5's live certificate contains 4,854
proof bindings and 237 named-rule applications, so the union-find explanation rather than e-graph
saturation dominates.

Local term and proof `let` bindings are valuable sharing, not merely printer noise. Recursively
inlining term bindings grew AC4 from 51 KB to 151 KB and doubled checking time; for AC5 it grew 276
KB to 943 KB and increased checking from 6.95 to about 17.4 seconds. Inlining the proof DAG already
slowed AC3 and expanding AC4 did not finish within 30 seconds. The next scaling step should select a
smaller explanation after saturation, or invoke a larger proved normalization rule, rather than
eliding the memo tables.

A paired AC4 measurement of the definitional-reduction fast path reduced the checked certificate
from 47,864 bytes and 1,279 lines to 43,106 bytes and 1,159 lines. Thirteen of the 48 live rewrite
applications used the direct form.

The proof forest and lazy congruence reasons then reduce the same AC4 and AC5 certificates as
follows. Lean times and memory are means of five fresh processes; they include process startup.

| Example | Metric | Eager parent proofs | Proof forest |
| --- | --- | ---: | ---: |
| AC4 | bytes | 43,106 | 11,823 |
|  | lines | 1,159 | 345 |
|  | live proof bindings | 851 | 225 |
|  | live rewrite applications | 48 | 16 |
|  | Lean time | 0.858 s | 0.382 s |
|  | peak memory | 546 MB | 480 MB |
| AC5 | bytes | 244,277 | 17,771 |
|  | lines | 6,011 | 510 |
|  | live proof bindings | 4,566 | 334 |
|  | live rewrite applications | 239 | 22 |
|  | Lean time | 6.262 s | 0.464 s |
|  | peak memory | 1,800 MB | 493 MB |

The post-saturation arena also shrinks, from 1,236 to 972 nodes for AC4 and from 6,452 to 4,872 for
AC5. This is a smaller reduction than the live certificate because non-definitional named rewrites
still build their normalization proofs eagerly. The generated certificates are kept in
`proofs/AC4.lean` and `proofs/AC5.lean`.
