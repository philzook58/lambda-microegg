"""A small, slow reference implementation of Lambda MicroEgg.

This stays close to Max Willsey's microegg.  The two additions are fat IDs,
which remember how an e-class's intrinsic context sits in the current context,
and capture-avoiding substitution.  Scans are preferred over extra indexes so
that the binding operations remain visible.
"""

from dataclasses import dataclass, field
from itertools import combinations
from typing import Callable


@dataclass(frozen=True)
class Lift:
    """An order-preserving injection into a context of size ``cod``."""

    positions: tuple[int, ...]
    cod: int

    def __post_init__(self):
        assert all(0 <= i < self.cod for i in self.positions)
        assert all(i < j for i, j in zip(self.positions, self.positions[1:]))

    @staticmethod
    def identity(n: int) -> "Lift":
        return Lift(tuple(range(n)), n)

    @staticmethod
    def empty(n: int) -> "Lift":
        return Lift((), n)

    def compose(self, small: "Lift") -> "Lift":
        """Compose ``small -> self's domain -> self's codomain``."""
        assert self.dom == small.cod
        return Lift(tuple(self.positions[i] for i in small.positions), self.cod)

    @property
    def dom(self) -> int:
        return len(self.positions)

    def extend(self, keep_last: bool) -> "Lift":
        positions = self.positions + ((self.cod,) if keep_last else ())
        return Lift(positions, self.cod + 1)


@dataclass(frozen=True)
class FatId:
    raw: int
    lift: Lift

    @property
    def ctx(self) -> int:
        return self.lift.cod

    def weaken(self, by: Lift) -> "FatId":
        assert self.ctx == by.dom
        return FatId(self.raw, by.compose(self.lift))

    def in_context(self, ctx: int) -> "FatId":
        assert ctx >= self.ctx
        return FatId(self.raw, Lift(self.lift.positions, ctx))

    def remove_unused(self, level: int) -> "FatId | None":
        """Delete an ambient context variable if this ID does not depend on it."""
        assert 0 <= level < self.ctx
        if level in self.lift.positions:
            return None
        positions = tuple(i - (i > level) for i in self.lift.positions)
        return FatId(self.raw, Lift(positions, self.ctx - 1))


type Id = FatId


class Term:
    def __sub__(self, other: "Term") -> "App":
        assert isinstance(other, Term)
        return App("-", (self, other))

    def size(self) -> int:
        match self:
            case App(_f, args):
                return 1 + sum(arg.size() for arg in args)
            case Lam(body):
                return 1 + body.size()
            case BVar() | Var():
                return 1
            case _:
                raise ValueError(f"unexpected term: {self}")


@dataclass(frozen=True)
class App(Term):
    f: object
    args: tuple[Term, ...] = ()


@dataclass(frozen=True)
class Lam(Term):
    body: Term


@dataclass(frozen=True)
class BVar(Term):
    """A de Bruijn index: zero is the nearest binder."""

    index: int


@dataclass(frozen=True)
class Var(Term):
    """A first-order pattern variable."""

    name: str


@dataclass(frozen=True)
class Subst(Term):
    """Substitute ``replacement`` for the binder surrounding ``body``."""

    body: Term
    replacement: Term


type Substitution = dict[str, FatId]


_BOUND = object()
_LAM = object()


@dataclass(frozen=True)
class Node:
    f: object
    args: tuple[FatId, ...] = ()


def _factor_lifts(target: Lift, edge: Lift) -> list[Lift]:
    """Find ``by`` such that ``by.compose(edge) == target``."""
    if target.dom != edge.dom or edge.cod > target.cod:
        return []
    return [
        by
        for chosen in combinations(range(target.cod), edge.cod)
        if (by := Lift(chosen, target.cod)).compose(edge) == target
    ]


@dataclass
class EGraph:
    memo: dict[Node, int] = field(default_factory=dict)
    uf: list[FatId] = field(default_factory=list)
    scope: list[int] = field(default_factory=list)

    def _make_set(self, scope: int) -> FatId:
        raw = len(self.uf)
        result = FatId(raw, Lift.identity(scope))
        self.uf.append(result)
        self.scope.append(scope)
        return result

    def find(self, id: FatId) -> FatId:
        while self.uf[id.raw].raw != id.raw:
            edge = self.uf[id.raw]
            id = FatId(edge.raw, id.lift.compose(edge.lift))
        return id

    def _add_node(self, scope: int, node: Node) -> FatId:
        raw = self.memo.get(node)
        if raw is not None:
            return self.find(FatId(raw, Lift.identity(scope)))
        result = self._make_set(scope)
        self.memo[node] = result.raw
        return result

    def bound(self, ctx: int, index: int) -> FatId:
        """Insert a de Bruijn variable into ``ctx``."""
        assert 0 <= index < ctx
        base = self._add_node(1, Node(_BOUND))
        return base.weaken(Lift((ctx - 1 - index,), ctx))

    def atom(self, f: object, ctx: int = 0) -> FatId:
        return self._add_node(0, Node(f)).weaken(Lift.empty(ctx))

    def app(self, f: object, args: tuple[FatId, ...], ctx: int | None = None) -> FatId:
        if not args:
            assert ctx is not None
            return self.atom(f, ctx)
        ctx = args[0].ctx
        assert all(arg.ctx == ctx for arg in args)
        args = tuple(self.find(arg) for arg in args)
        used = tuple(sorted({i for arg in args for i in arg.lift.positions}))
        where = {level: i for i, level in enumerate(used)}
        core = tuple(
            FatId(arg.raw, Lift(tuple(where[i] for i in arg.lift.positions), len(used)))
            for arg in args
        )
        return self._add_node(len(used), Node(f, core)).weaken(Lift(used, ctx))

    def lam(self, body: FatId) -> FatId:
        assert body.ctx > 0
        body = self.find(body)
        outer_ctx = body.ctx - 1
        outer = tuple(i for i in body.lift.positions if i < outer_ctx)
        uses_bound = outer_ctx in body.lift.positions
        core_positions = tuple(range(len(outer))) + (
            (len(outer),) if uses_bound else ()
        )
        core_body = FatId(body.raw, Lift(core_positions, len(outer) + 1))
        return self._add_node(len(outer), Node(_LAM, (core_body,))).weaken(
            Lift(outer, outer_ctx)
        )

    def add_term(
        self,
        term: Term,
        subst: Substitution | None = None,
        ctx: int = 0,
    ) -> FatId:
        subst = {} if subst is None else subst
        match term:
            case Var(name):
                return subst[name]
            case BVar(index):
                return self.bound(ctx, index)
            case Lam(body):
                return self.lam(self.add_term(body, subst, ctx + 1))
            case Subst(body, replacement):
                body_id = self.add_term(body, subst, ctx + 1)
                replacement_id = self.add_term(replacement, subst, ctx)
                return self.substitute(body_id, ctx, replacement_id)
            case App(f, args):
                ids = tuple(self.add_term(arg, subst, ctx) for arg in args)
                return self.app(f, ids, ctx)
            case _:
                raise ValueError(f"unexpected term: {term}")

    def _link(self, child: int, parent: FatId):
        assert self.uf[child].raw == child != parent.raw
        self.uf[child] = parent

    def _union(self, left: FatId, right: FatId) -> bool:
        assert left.ctx == right.ctx
        left, right = self.find(left), self.find(right)
        if left == right:
            return False

        if left.raw == right.raw:
            kept = tuple(
                i
                for i, (a, b) in enumerate(
                    zip(left.lift.positions, right.lift.positions)
                )
                if a == b
            )
            root = self._make_set(len(kept))
            self._link(left.raw, FatId(root.raw, Lift(kept, left.lift.dom)))
            return True

        common = tuple(i for i in left.lift.positions if i in set(right.lift.positions))
        to_left = Lift(
            tuple(left.lift.positions.index(i) for i in common), left.lift.dom
        )
        to_right = Lift(
            tuple(right.lift.positions.index(i) for i in common), right.lift.dom
        )
        if common == right.lift.positions:
            self._link(left.raw, FatId(right.raw, to_left))
        elif common == left.lift.positions:
            self._link(right.raw, FatId(left.raw, to_right))
        else:
            root = self._make_set(len(common))
            self._link(left.raw, FatId(root.raw, to_left))
            self._link(right.raw, FatId(root.raw, to_right))
        return True

    def union(self, left: Term, right: Term, ctx: int = 0):
        self._union(self.add_term(left, ctx=ctx), self.add_term(right, ctx=ctx))
        self.rebuild()

    def _is_eq(self, left: FatId, right: FatId) -> bool:
        return self.find(left) == self.find(right)

    def is_eq(self, left: Term, right: Term, ctx: int = 0) -> bool:
        return self._is_eq(self.add_term(left, ctx=ctx), self.add_term(right, ctx=ctx))

    def nodes_in_class(self, id: FatId) -> list[tuple[Node, Lift]]:
        """Return nodes together with their placement in ``id``'s context."""
        id = self.find(id)
        result = []
        for node, raw in self.memo.items():
            origin = FatId(raw, Lift.identity(self.scope[raw]))
            edge = self.find(origin)
            if edge.raw == id.raw:
                result.extend((node, by) for by in _factor_lifts(id.lift, edge.lift))
        return result

    def _canonical_node(self, node: Node) -> tuple[Lift, Node]:
        if node.f is _BOUND:
            return Lift.identity(1), node
        if node.f is _LAM:
            body = self.find(node.args[0])
            outer_ctx = body.ctx - 1
            outer = tuple(i for i in body.lift.positions if i < outer_ctx)
            uses_bound = outer_ctx in body.lift.positions
            core_positions = tuple(range(len(outer))) + (
                (len(outer),) if uses_bound else ()
            )
            return (
                Lift(outer, outer_ctx),
                Node(_LAM, (FatId(body.raw, Lift(core_positions, len(outer) + 1)),)),
            )
        if not node.args:
            return Lift.identity(0), node

        args = tuple(self.find(arg) for arg in node.args)
        ctx = args[0].ctx
        used = tuple(sorted({i for arg in args for i in arg.lift.positions}))
        where = {level: i for i, level in enumerate(used)}
        core = tuple(
            FatId(arg.raw, Lift(tuple(where[i] for i in arg.lift.positions), len(used)))
            for arg in args
        )
        return Lift(used, ctx), Node(node.f, core)

    def rebuild(self):
        while True:
            old_memo, self.memo = self.memo, {}
            changed = False
            for node, raw in old_memo.items():
                old = FatId(raw, Lift.identity(self.scope[raw]))
                lift, node = self._canonical_node(node)
                existing = self.memo.get(node)
                if existing is None:
                    if lift == Lift.identity(self.scope[raw]):
                        self.memo[node] = raw
                        base = old
                    else:
                        base = self._make_set(lift.dom)
                        self.memo[node] = base.raw
                else:
                    base = self.find(FatId(existing, Lift.identity(lift.dom)))
                changed |= self._union(old, base.weaken(lift))
            if not changed:
                return

    def ematch(self, pattern: Term, id: FatId) -> list[Substitution]:
        return self._ematch(pattern, self.find(id), {})

    def _ematch(
        self, pattern: Term, id: FatId, subst: Substitution
    ) -> list[Substitution]:
        id = self.find(id)
        match pattern:
            case Var(name):
                if name not in subst:
                    return [{**subst, name: id}]
                return [subst] if self.find(subst[name]) == id else []
            case BVar(index):
                level = id.ctx - 1 - index
                return [
                    subst
                    for node, by in self.nodes_in_class(id)
                    if node.f is _BOUND and by.positions == (level,)
                ]
            case Lam(body_pattern):
                results = []
                for node, by in self.nodes_in_class(id):
                    if node.f is _LAM:
                        body = node.args[0].weaken(by.extend(True))
                        results.extend(self._ematch(body_pattern, body, subst))
                return results
            case App(f, args):
                results = []
                for node, by in self.nodes_in_class(id):
                    if node.f != f or len(node.args) != len(args):
                        continue
                    todo = [subst]
                    for arg_pattern, arg in zip(args, node.args):
                        target = arg.weaken(by)
                        todo = [
                            out
                            for current in todo
                            for out in self._ematch(arg_pattern, target, current)
                        ]
                    results.extend(todo)
                return results
            case _:
                raise ValueError(f"unsupported match pattern: {pattern}")

    def rw(self, lhs: Term, rhs: Term):
        matches = []
        for raw, scope in enumerate(self.scope):
            target = FatId(raw, Lift.identity(scope))
            matches.extend((target, subst) for subst in self.ematch(lhs, target))
        # Search and apply are deliberately separate, as in microegg.
        for target, subst in matches:
            self._union(target, self.add_term(rhs, subst, target.ctx))
        self.rebuild()

    def substitute(self, body: FatId, level: int, replacement: FatId) -> FatId:
        """Capture-avoiding substitution of one ambient context variable."""
        assert body.ctx == replacement.ctx + 1
        assert 0 <= level < body.ctx
        self.rebuild()
        result = self._substitute(body, level, replacement, {})
        self.rebuild()
        return self.find(result)

    def _substitute(
        self,
        body: FatId,
        level: int,
        replacement: FatId,
        memo: dict[tuple[FatId, int, FatId], FatId],
    ) -> FatId:
        body, replacement = self.find(body), self.find(replacement)
        projected = body.remove_unused(level)
        if projected is not None:
            return projected
        # A normalized version could memoize (raw ID, intrinsic slot,
        # replacement raw ID, dependency overlap), then reapply the result lift.
        # Using fat IDs here records that overlap directly.
        key = body, level, replacement
        if key in memo:
            return memo[key]
        # Beneath a lambda, the same cycle can return with one more unused
        # trailing context variable. Reuse the earlier placeholder in that larger
        # context instead of missing the cycle because the fat IDs differ.
        for (old_body, old_level, old_replacement), old_result in memo.items():
            if (
                old_level == level
                and old_body.raw == body.raw
                and old_replacement.raw == replacement.raw
                and old_body.ctx <= body.ctx
                and old_replacement.ctx <= replacement.ctx
                and old_body.in_context(body.ctx) == body
                and old_replacement.in_context(replacement.ctx) == replacement
            ):
                return old_result.in_context(body.ctx - 1)

        result = self._make_set(body.ctx - 1)
        memo[key] = result  # tie recursive e-classes back to this placeholder
        for node, by in list(self.nodes_in_class(body)):
            if node.f is _BOUND:
                old_level = by.positions[0]
                translated = (
                    replacement
                    if old_level == level
                    else self.bound(
                        body.ctx - 1, body.ctx - 2 - (old_level - (old_level > level))
                    )
                )
            elif node.f is _LAM:
                inner = node.args[0].weaken(by.extend(True))
                under_binder = replacement.in_context(body.ctx)
                translated = self.lam(
                    self._substitute(inner, level, under_binder, memo)
                )
            else:
                args = tuple(
                    self._substitute(arg.weaken(by), level, replacement, memo)
                    for arg in node.args
                )
                translated = self.app(node.f, args, body.ctx - 1)
            self._union(result, translated)
        return self.find(result)

    def extract(
        self,
        term: Term,
        cost: Callable[[Term], float] = Term.size,
        ctx: int = 0,
    ) -> Term:
        id = self.add_term(term, ctx=ctx)
        self.rebuild()
        result = self._extract(self.find(id), {}, set(), cost)
        assert result is not None
        return result

    def _extract(
        self,
        id: FatId,
        memo: dict[FatId, Term | None],
        active: set[int],
        cost: Callable[[Term], float],
    ) -> Term | None:
        id = self.find(id)
        if id in memo:
            return memo[id]
        if id.raw in active:
            return None
        active.add(id.raw)
        best: Term | None = None
        for node, by in self.nodes_in_class(id):
            if node.f is _BOUND:
                candidate: Term = BVar(id.ctx - 1 - by.positions[0])
            elif node.f is _LAM:
                body = self._extract(
                    node.args[0].weaken(by.extend(True)), memo, active, cost
                )
                if body is None:
                    continue
                candidate = Lam(body)
            else:
                args = tuple(
                    self._extract(arg.weaken(by), memo, active, cost)
                    for arg in node.args
                )
                if any(arg is None for arg in args):
                    continue
                candidate = App(node.f, args)  # type: ignore[arg-type]
            if best is None or cost(candidate) < cost(best):
                best = candidate
        active.remove(id.raw)
        memo[id] = best
        return best


def Consts(names: str) -> list[App]:
    return [App(name) for name in names.split()]


def Function(name: str):
    return lambda *args: App(name, args)


def Vars(names: str) -> list[Var]:
    return [Var(name) for name in names.split()]


def test_egraph():
    egraph = EGraph()
    a, b, c = Consts("a b c")
    x, y = Vars("x y")
    sub = Function("-")
    egraph.add_term(sub(a, b))
    assert len(egraph.uf) == 3
    egraph.add_term(sub(a, b))
    assert len(egraph.uf) == 3
    egraph.union(sub(a, b), c)
    assert egraph.is_eq(a - b, c)
    egraph.rw(sub(x, y), sub(y, x))
    assert egraph.extract(sub(b, a)) == c


def test_fat_ids_and_substitution():
    egraph = EGraph()
    pair = Function("pair")

    # Only the nearest variable is retained in the term's intrinsic context.
    term = egraph.add_term(pair(BVar(0), App("constant")), ctx=2)
    assert term.ctx == 2 and term.lift.positions == (1,)

    # [x := fred] x = fred.
    assert egraph.extract(Subst(BVar(0), App("fred"))) == App("fred")

    # Substitution under a lambda shifts the free replacement and avoids capture.
    capture_test = Subst(Lam(BVar(1)), BVar(0))
    assert egraph.extract(capture_test, ctx=1) == Lam(BVar(1))

    # An unused variable is deleted by changing the fat ID alone.
    assert egraph.extract(Subst(App("constant"), App("ignored"))) == App("constant")

    # A recursive class may recur under a binder with a larger ambient context.
    cyclic = EGraph()
    x = cyclic.bound(1, 0)
    cyclic._union(x, cyclic.lam(x.in_context(2)))
    cyclic.rebuild()
    fred = cyclic.atom("fred")
    assert cyclic.extract(Subst(BVar(0), App("fred"))) == App("fred")
    assert cyclic.find(cyclic.substitute(x, 0, fred)) == cyclic.find(fred)


if __name__ == "__main__":
    test_egraph()
    test_fat_ids_and_substitution()
