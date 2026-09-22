//! Two ways of naming a variable:
//!
//! - a de Bruijn index counts outward from the nearest binder;
//! - a de Bruijn level counts a variable coming down from an ambient context.
//!
//! - Note that both of these concepts are beside the main point from that of a thinning/lifting
//!
//! During pattern matching, `top_ctx` is the ambient context at the top of the
//! pattern, and `current_ctx` additionally includes the variables introduced
//! locally by binders inside the pattern. A pattern variable has to be carried
//! up to the context at the top of the pattern in order to be carried over to
//! the right-hand side. Miller patterns describe how you want that carrying to
//! work, and which variables you want to allow in the pattern variable.
//!
//! A lift embeds one context into another by adding unused variables.

use indexmap::IndexMap;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;
use symbol_table::GlobalSymbol as Symbol;
use web_time::{Duration, Instant};

mod terms;
pub use terms::{NamedTerm, Pattern, Rewrite, Term, TermCtx};

pub type RawId = u32;

/// A de Bruijn index: zero names the nearest enclosing binder.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct DeBruijnIndex(usize);

impl DeBruijnIndex {
    pub fn new(index: usize) -> Self {
        Self(index)
    }
    pub fn get(self) -> usize {
        self.0
    }
    pub fn to_level(self, context_len: usize) -> Option<DeBruijnLevel> {
        Some(DeBruijnLevel(
            context_len.checked_sub(self.0.checked_add(1)?)?,
        ))
    }
}

impl From<usize> for DeBruijnIndex {
    fn from(index: usize) -> Self {
        Self(index)
    }
}

/// A de Bruijn level: zero names the outermost variable in a context.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeBruijnLevel(usize);

impl DeBruijnLevel {
    pub fn new(level: usize) -> Self {
        Self(level)
    }
    pub fn get(self) -> usize {
        self.0
    }
}

impl From<usize> for DeBruijnLevel {
    fn from(level: usize) -> Self {
        Self(level)
    }
}

/// Convert distinct pattern-local indices to levels in the current context.
fn local_indices_to_levels(
    top_ctx: usize,
    current_ctx: usize, // == top context + # of bound variables
    arguments: &[DeBruijnIndex],
) -> Option<SmallVec<[DeBruijnLevel; 4]>> {
    let local_depth = current_ctx.checked_sub(top_ctx)?;
    if arguments.iter().any(|index| index.get() >= local_depth)
        || arguments
            .iter()
            .enumerate()
            .any(|(i, index)| arguments[..i].contains(index))
    {
        return None;
    }
    arguments
        .iter()
        .map(|index| index.to_level(current_ctx))
        .collect()
}

/// Bring down `top context + Miller arguments` into the current context. Match
/// arguments are required to be written in this outer-to-inner order.
#[inline(always)]
fn occurrence_lift(
    top_ctx: usize,
    current_ctx: usize,
    arguments: &[DeBruijnIndex],
) -> Option<Lift> {
    // First-order metavariables are overwhelmingly common. They keep the
    // whole top context and none of the binders introduced inside the rule.
    if arguments.is_empty() {
        current_ctx.checked_sub(top_ctx)?;
        return Some(Lift::from_bits(Lift::mask(top_ctx), current_ctx));
    }
    let levels = local_indices_to_levels(top_ctx, current_ctx, arguments)?;
    if !levels.windows(2).all(|pair| pair[0] < pair[1]) {
        return None;
    }
    let selected: SmallVec<[usize; 8]> = (0..top_ctx)
        .chain(levels.iter().map(|level| level.get()))
        .collect();
    Some(Lift::selected(current_ctx, &selected))
}

#[inline(always)]
fn pattern_occurrence_lift(
    top_ctx: usize,
    current_ctx: usize,
    arguments: &[Pattern],
) -> Option<Lift> {
    if arguments.is_empty() {
        occurrence_lift(top_ctx, current_ctx, &[])
    } else {
        let indices = Pattern::miller_indices(arguments)?;
        occurrence_lift(top_ctx, current_ctx, &indices)
    }
}

/// An order-preserving injection into an
/// an ambient context. The leading 1 records the codomain length; lower bits
/// select where each domain variable occurs in that codomain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Lift(u8);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Union {
    lift: Lift,
    left: Lift,
    right: Lift,
}

// Yeaaa, I dunno that Pullback is that useful of a framing, but it is evocative of the right square
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pullback {
    diagonal: Lift,
    from_left: Lift,
    from_right: Lift,
}

impl Lift {
    fn mask(n: usize) -> u8 {
        assert!(n <= 7, "packed IDs support at most 7 context variables");
        if n == 0 { 0 } else { (1u8 << n) - 1 }
    }
    fn from_bits(bits: u8, n: usize) -> Self {
        let mask = Self::mask(n);
        Self((1u8 << n) | (bits & mask))
    }
    pub fn identity(n: usize) -> Self {
        Self::from_bits(Self::mask(n), n)
    }
    fn unused(n: usize) -> Self {
        Self::from_bits(0, n)
    }
    pub fn select(n: usize, i: usize) -> Self {
        assert!(i < n);
        Self::from_bits(1u8 << i, n)
    }
    fn selected(n: usize, indices: &[usize]) -> Self {
        let bits = indices.iter().fold(0, |bits, &i| {
            assert!(i < n);
            bits | (1u8 << i)
        });
        Self::from_bits(bits, n)
    }
    pub fn cod(&self) -> usize {
        (7 - self.0.leading_zeros()) as usize
    }
    fn selected_bits(&self) -> u8 {
        self.0 & Self::mask(self.cod())
    }
    pub fn dom(&self) -> usize {
        self.selected_bits().count_ones() as usize
    }
    pub fn get(&self, i: usize) -> bool {
        assert!(i < self.cod());
        self.selected_bits() & (1u8 << i) != 0
    }
    fn prefix(&self, n: usize) -> Self {
        assert!(n <= self.cod());
        Self::from_bits(self.selected_bits(), n)
    }
    fn append(&self, keep: bool) -> Self {
        Self::from_bits(
            self.selected_bits() | ((keep as u8) << self.cod()),
            self.cod() + 1,
        )
    }
    fn remove(&self, index: usize) -> Option<Self> {
        assert!(index < self.cod());
        if self.get(index) {
            return None;
        }
        let low_mask = Self::mask(index);
        let low = self.selected_bits() & low_mask;
        let high = (self.selected_bits() >> (index + 1)) << index;
        Some(Self::from_bits(low | high, self.cod() - 1))
    }
    fn is_identity(&self) -> bool {
        self.selected_bits() == Self::mask(self.cod())
    }
    pub fn compose(&self, small: &Self) -> Self {
        assert_eq!(self.dom(), small.cod());
        let mut bits = 0;
        let mut j = 0;
        for i in 0..self.cod() {
            if self.get(i) {
                if small.get(j) {
                    bits |= 1u8 << i;
                }
                j += 1;
            }
        }
        Self::from_bits(bits, self.cod())
    }
    /// Factor `target` through this lift. If `self : A -> Γ` and
    /// `target : B -> Γ`, return the unique ordered lift `B -> A`.
    fn factor(&self, target: &Self) -> Option<Self> {
        if self.cod() != target.cod() {
            return None;
        }
        let mut bits = 0;
        let mut position = 0;
        for level in 0..self.cod() {
            if target.get(level) && !self.get(level) {
                return None;
            }
            if self.get(level) {
                if target.get(level) {
                    bits |= 1u8 << position;
                }
                position += 1;
            }
        }
        Some(Self::from_bits(bits, self.dom()))
    }
    /// Form the union of two subcontexts of one shared ambient context.
    /// This is their coproduct in the subcontext lattice.
    ///
    /// ```text
    ///              A             B
    ///               \           /
    ///              left       right
    ///                 \       /
    ///               used union U
    ///                     |
    ///                   lift
    ///                     v
    ///                 ambient Γ
    /// ```
    ///
    /// `lift.compose(left) == self` and
    /// `lift.compose(right) == other`.
    fn union(&self, other: &Self) -> Union {
        assert_eq!(self.cod(), other.cod());
        let union = Self::from_bits(self.selected_bits() | other.selected_bits(), self.cod());
        let mut left = 0;
        let mut right = 0;
        let mut j = 0;
        for i in 0..self.cod() {
            if union.get(i) {
                if self.get(i) {
                    left |= 1u8 << j;
                }
                if other.get(i) {
                    right |= 1u8 << j;
                }
                j += 1;
            }
        }
        Union {
            lift: union,
            left: Self::from_bits(left, j),
            right: Self::from_bits(right, j),
        }
    }
    /// Pull back two lifts into a shared ambient context. The pullback object
    /// is their meet: the intersection of their dependency subcontexts.
    ///
    /// ```text
    ///                 intersection P
    ///                    /     \
    ///           from_left     from_right
    ///                  /         \
    ///                  A         B
    ///                   \       /
    ///                 self     other
    ///                    \     /
    ///                   ambient Γ
    /// ```
    ///
    /// `self.compose(from_left) == diagonal` and
    /// `other.compose(from_right) == diagonal`.
    fn pullback(&self, other: &Self) -> Pullback {
        assert_eq!(self.cod(), other.cod());
        let diagonal = Self::from_bits(self.selected_bits() & other.selected_bits(), self.cod());
        let mut left = 0;
        let mut right = 0;
        let mut a = 0;
        let mut b = 0;
        for i in 0..self.cod() {
            if self.get(i) {
                if other.get(i) {
                    left |= 1u8 << a;
                }
                a += 1;
            }
            if other.get(i) {
                if self.get(i) {
                    right |= 1u8 << b;
                }
                b += 1;
            }
        }
        Pullback {
            diagonal,
            from_left: Self::from_bits(left, a),
            from_right: Self::from_bits(right, b),
        }
    }
    /// Largest subcontext of their shared domain on which the two lifts agree
    /// context variable by context variable.
    fn equalizer(&self, other: &Self) -> Self {
        assert_eq!(self.cod(), other.cod());
        assert_eq!(self.dom(), other.dom());
        let left = (0..self.cod()).filter(|&i| self.get(i));
        let right = (0..other.cod()).filter(|&i| other.get(i));
        let bits = left
            .zip(right)
            .enumerate()
            .fold(0, |bits, (i, (left, right))| {
                bits | (u8::from(left == right) << i)
            });
        Self::from_bits(bits, self.dom())
    }
    pub fn bits(&self) -> String {
        (0..self.cod())
            .map(|i| if self.get(i) { '1' } else { '0' })
            .collect()
    }
}

/// Upper 8 bits encode the lift; lower 24 bits hold Max's raw ID.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Id(u32);

// These packed values are intentionally smaller than a machine register.
// Widening Lift (and therefore Id) should make us reconsider the inline
// capacities and layouts below rather than silently changing every hot type.
const _: () = {
    assert!(std::mem::size_of::<Lift>() == 1);
    assert!(std::mem::size_of::<Id>() == 4);
};

impl Id {
    const RAW_MASK: u32 = (1 << 24) - 1;
    fn new(lift: Lift, raw: RawId) -> Self {
        assert!(raw <= Self::RAW_MASK, "exhausted 24-bit raw IDs");
        Self(((lift.0 as u32) << 24) | raw)
    }
    pub fn lift(&self) -> Lift {
        Lift((self.0 >> 24) as u8)
    }
    pub fn raw(&self) -> RawId {
        self.0 & Self::RAW_MASK
    }
    pub fn ctx(&self) -> usize {
        self.lift().cod()
    }
    fn weaken(&self, by: &Lift) -> Self {
        Self::new(by.compose(&self.lift()), self.raw())
    }
    /// View the same e-class in a prefix-related context. Growing the
    /// context introduces unused variables. Shrinking is legal only when
    /// none of the discarded variables occur in the ID's lift.
    pub fn in_context(&self, ctx: usize) -> Option<Self> {
        let old_ctx = self.ctx();
        if ctx < old_ctx && (ctx..old_ctx).any(|i| self.lift().get(i)) {
            return None;
        }
        Some(Self::new(
            Lift::from_bits(self.lift().selected_bits(), ctx),
            self.raw(),
        ))
    }
    fn remove_context_variable(&self, index: usize) -> Option<Self> {
        Some(Self::new(self.lift().remove(index)?, self.raw()))
    }
    pub fn show(&self) -> String {
        if self.lift().is_identity() {
            format!("e{}", self.raw())
        } else {
            format!("l_{}(e{})", self.lift().bits(), self.raw())
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    Var,
    Atom(Symbol),
    /// One step of binary, curried application.
    App(Id, Id),
    Binder(Symbol, Id),
}

/// An e-node's head, without its children, as passed to an extraction weight
/// function. Weights cannot depend on children: the extractor sums node
/// weights, so a subterm's cost never depends on where it is used.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Head {
    Var,
    Atom(Symbol),
    App,
    Binder(Symbol),
}

/// The variable a `Node::Var` placement denotes, or `None` when the placement
/// does not select exactly one ambient variable.
fn var_term(by: &Lift, ctx: usize, root_scope: usize) -> Option<Term> {
    if by.dom() != 1 {
        return None;
    }
    let index = (0..by.cod()).find(|&i| by.get(i))?;
    if index < root_scope {
        Some(Term::FVar(index.into()))
    } else {
        Some(Term::BVar(ctx.checked_sub(index + 1)?.into()))
    }
}

/// An e-node's children, lifted into the placement `by`. A binder's body
/// lives one context deeper, so its lift gains the bound variable.
fn node_children(node: &Node, by: &Lift) -> impl Iterator<Item = Id> {
    let (children, under_binder): (SmallVec<[Id; 2]>, bool) = match node {
        Node::Var | Node::Atom(_) => (SmallVec::new(), false),
        Node::App(function, argument) => (smallvec::smallvec![*function, *argument], false),
        Node::Binder(_, body) => (smallvec::smallvec![*body], true),
    };
    let by = if under_binder { by.append(true) } else { *by };
    children.into_iter().map(move |child| child.weaken(&by))
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RunStats {
    /// Rounds that changed the e-graph. A final no-change check is not counted.
    pub rounds: usize,
    /// Successful unions requested directly by rewrite applications.
    pub unions: usize,
    pub match_time: Duration,
    pub apply_time: Duration,
    pub rebuild_time: Duration,
}

impl RunStats {
    pub fn total_time(&self) -> Duration {
        self.match_time + self.apply_time + self.rebuild_time
    }
}

/// Match results contain only fat IDs. A binding for an n-ary metavariable
/// lives in `top_ctx + n`; its lift records unused top variables and formals.
#[derive(Clone, Default)]
pub struct Subst(SmallVec<[(Symbol, Id); 3]>);

// Three common bindings fit in one 32-byte value on 64-bit hosts. Treat a
// change here as a prompt to remeasure matcher allocation and cache behavior.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<Subst>() == 32);

type MatchResults = SmallVec<[Subst; 1]>;

impl Subst {
    fn get(&self, name: &Symbol) -> Option<&Id> {
        self.0
            .iter()
            .find_map(|(key, binding)| (*key == *name).then_some(binding))
    }
    fn insert(&mut self, name: Symbol, binding: Id) {
        self.0.push((name, binding));
    }
    pub fn bindings(&self) -> impl Iterator<Item = (&str, &Id)> + '_ {
        self.0
            .iter()
            .map(|(name, binding)| (name.as_str(), binding))
    }
}

impl std::ops::Index<&str> for Subst {
    type Output = Id;
    fn index(&self, name: &str) -> &Id {
        self.get(&name.into()).expect("unbound pattern variable")
    }
}

/// Find all W such that W.compose(edge) = target. A redundant edge may
/// admit several W, corresponding to different variables in the target.
fn factor_lifts(target: &Lift, edge: &Lift) -> SmallVec<[Lift; 2]> {
    if target.dom() != edge.dom() || edge.cod() > target.cod() {
        return SmallVec::new();
    }
    if edge.is_identity() {
        return smallvec::smallvec![*target];
    }
    fn visit(
        target: &Lift,
        edge: &Lift,
        source: usize,
        next: usize,
        chosen: &mut SmallVec<[usize; 8]>,
        out: &mut SmallVec<[Lift; 2]>,
    ) {
        if source == edge.cod() {
            let by = Lift::selected(target.cod(), chosen);
            if by.compose(edge) == *target {
                out.push(by);
            }
            return;
        }
        let remaining = edge.cod() - source - 1;
        for index in next..target.cod().saturating_sub(remaining) {
            if target.get(index) == edge.get(source) {
                chosen.push(index);
                visit(target, edge, source + 1, index + 1, chosen, out);
                chosen.pop();
            }
        }
    }
    let mut out = SmallVec::new();
    visit(target, edge, 0, 0, &mut SmallVec::new(), &mut out);
    out
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MatchMode {
    /// Match one canonical placement of each stored enode. This is the mode
    /// rewriting uses, so a redundant union-find edge cannot multiply work.
    Canonical,
    /// Enumerate every placement admitted by a lift. Useful when a
    /// caller explicitly wants all ambient-variable occurrences.
    Lifted,
}

#[derive(Clone, Default)]
pub struct EGraph {
    parent: Vec<Id>,
    memo: IndexMap<Node, RawId, rustc_hash::FxBuildHasher>,
    rev: IndexMap<RawId, Vec<(Node, Lift)>, rustc_hash::FxBuildHasher>,
    // Possible next performance experiments, deliberately not implemented:
    // cache canonical targets and root-operator buckets while rebuilding, or
    // give each Rewrite fixed metavariable slots to shrink retained matches.
    // Incremental rebuild and semi-naive matching are larger design changes.
    /// Keep `rev` usable between construction and the batch's final rebuild
    /// when a constructive Miller permutation needs class-local traversal.
    rev_tracked: bool,
    rev_valid: bool,
    rebuild_time_total: Duration,
}

impl EGraph {
    pub fn new() -> Self {
        Self::default()
    }
    fn make_set(&mut self, scope: usize) -> Id {
        assert!(
            self.parent.len() <= Id::RAW_MASK as usize,
            "exhausted 24-bit raw IDs"
        );
        self.rev_valid = false;
        let raw = self.parent.len() as RawId;
        let id = Id::new(Lift::identity(scope), raw);
        self.parent.push(id);
        id
    }
    /// The identity placement of a raw class in its own intrinsic context.
    #[inline(always)]
    fn origin(&self, raw: RawId) -> Id {
        Id::new(Lift::identity(self.parent[raw as usize].ctx()), raw)
    }
    pub fn find(&self, id: &Id) -> Id {
        let mut out = *id;
        loop {
            let edge = &self.parent[out.raw() as usize];
            if edge.raw() == out.raw() {
                return out;
            }
            out = Id::new(out.lift().compose(&edge.lift()), edge.raw());
        }
    }
    fn find_mut(&mut self, id: &Id) -> Id {
        if self.parent[id.raw() as usize].raw() == id.raw() {
            return *id;
        }
        // Walk to the root iteratively. Recursing once per union-find edge
        // overflowed the stack on long chains, and chain length is an
        // internal artifact rather than anything the caller controls.
        let mut path: SmallVec<[RawId; 16]> = SmallVec::new();
        let mut current = id.raw();
        loop {
            let edge = self.parent[current as usize];
            if edge.raw() == current {
                break;
            }
            path.push(current);
            current = edge.raw();
        }
        let root_raw = current;
        // Compress from the root backwards, so each node composes through a
        // successor that already points straight at the root. Path
        // compression stores an edge in the raw class's intrinsic context;
        // `id` itself may be placed in a larger ambient context.
        for &raw in path.iter().rev() {
            let edge = self.parent[raw as usize];
            if edge.raw() == root_raw {
                continue;
            }
            let next = self.parent[edge.raw() as usize];
            debug_assert_eq!(next.raw(), root_raw);
            debug_assert_eq!(next.ctx(), edge.lift().dom());
            self.parent[raw as usize] = Id::new(edge.lift().compose(&next.lift()), root_raw);
        }
        let root = self.parent[id.raw() as usize];
        debug_assert_eq!(root.raw(), root_raw);
        Id::new(id.lift().compose(&root.lift()), root.raw())
    }
    fn intern(&mut self, scope: usize, node: Node) -> Id {
        if let Some(&raw) = self.memo.get(&node) {
            return self.find_mut(&Id::new(Lift::identity(scope), raw));
        }
        let id = self.make_set(scope);
        if self.rev_tracked {
            self.rev
                .entry(id.raw())
                .or_default()
                .push((node.clone(), Lift::identity(scope)));
        }
        self.memo.insert(node, id.raw());
        id
    }
    pub fn var(&mut self, ctx: usize, index: usize) -> Id {
        let base = self.intern(1, Node::Var);
        base.weaken(&Lift::select(ctx, index))
    }
    pub fn atom(&mut self, name: &str, ctx: usize) -> Id {
        self.atom_symbol(name.into(), ctx)
    }
    fn atom_symbol(&mut self, name: Symbol, ctx: usize) -> Id {
        let base = self.intern(0, Node::Atom(name));
        base.weaken(&Lift::unused(ctx))
    }
    pub fn apps(&mut self, op: &str, arguments: Vec<Id>) -> Id {
        assert!(!arguments.is_empty());
        let ctx = arguments[0].ctx();
        assert!(arguments.iter().all(|argument| argument.ctx() == ctx));
        let mut application = self.atom(op, ctx);
        for argument in arguments {
            application = self.app(application, argument);
        }
        application
    }
    pub fn app(&mut self, function: Id, argument: Id) -> Id {
        assert_eq!(function.ctx(), argument.ctx());
        let (common, node) = self.canonical_node(&Node::App(function, argument));
        let base = self.intern(common.dom(), node);
        base.weaken(&common)
    }
    /// The bound variable is the final variable in the body's context.
    pub fn binder(&mut self, op: &str, body: Id) -> Id {
        self.binder_symbol(op.into(), body)
    }
    fn binder_symbol(&mut self, op: Symbol, body: Id) -> Id {
        assert!(body.ctx() > 0);
        let (outer, node) = self.canonical_node(&Node::Binder(op, body));
        let base = self.intern(outer.dom(), node);
        base.weaken(&outer)
    }
    /// Return the pulled e-node and the lift back to its original context.
    fn canonical_node(&mut self, node: &Node) -> (Lift, Node) {
        match node {
            Node::Var => (Lift::identity(1), Node::Var),
            Node::Atom(s) => (Lift::identity(0), Node::Atom(*s)),
            Node::App(function, argument) => {
                let function = self.find_mut(function);
                let argument = self.find_mut(argument);
                if function.lift().is_identity() && argument.lift().is_identity() {
                    return (
                        Lift::identity(function.ctx()),
                        Node::App(function, argument),
                    );
                }
                let common = function.lift().union(&argument.lift()).lift;
                let function = Id::new(common.union(&function.lift()).right, function.raw());
                let argument = Id::new(common.union(&argument.lift()).right, argument.raw());
                (common, Node::App(function, argument))
            }
            Node::Binder(op, body) => {
                let body = self.find_mut(body);
                let outer = body.lift().prefix(body.ctx() - 1);
                let core_body = Id::new(
                    Lift::identity(outer.dom()).append(body.lift().get(body.ctx() - 1)),
                    body.raw(),
                );
                (outer, Node::Binder(*op, core_body))
            }
        }
    }
    /// Link two union-find roots, updating the reverse e-class index when a
    /// constructive rewrite has requested it. Congruence may still be dirty,
    /// but class-local traversals then remain cheap until the next rebuild.
    fn link_root(&mut self, child: RawId, parent: Id) {
        debug_assert_eq!(self.parent[child as usize].raw(), child);
        debug_assert_ne!(child, parent.raw());
        debug_assert_eq!(self.parent[child as usize].ctx(), parent.ctx());
        self.parent[child as usize] = parent;
        if self.rev_tracked
            && let Some(nodes) = self.rev.swap_remove(&child)
        {
            self.rev.entry(parent.raw()).or_default().extend(
                nodes
                    .into_iter()
                    .map(|(node, edge)| (node, edge.compose(&parent.lift()))),
            );
        }
    }
    pub fn union(&mut self, a: &Id, b: &Id) -> bool {
        assert_eq!(a.ctx(), b.ctx(), "equality needs a shared context");
        let a = self.find_mut(a);
        let b = self.find_mut(b);
        if a == b {
            return false;
        }
        self.rev_valid = false;
        if a.raw() == b.raw() {
            // Equating two placements of one class restricts that class to
            // the context variables on which the placements agree. For example,
            // f(x) = f(y) turns the result of f into a context-independent
            // value rather than treating x and y themselves as equal.
            let dependency = a.lift().equalizer(&b.lift());
            let root = self.make_set(dependency.dom());
            self.link_root(a.raw(), Id::new(dependency, root.raw()));
            return true;
        }
        let Pullback {
            diagonal: common,
            from_left: to_a,
            from_right: to_b,
        } = a.lift().pullback(&b.lift());
        if common == b.lift() {
            self.link_root(a.raw(), Id::new(to_a, b.raw()));
        } else if common == a.lift() {
            self.link_root(b.raw(), Id::new(to_b, a.raw()));
        } else {
            let root = self.make_set(common.dom());
            self.link_root(a.raw(), Id::new(to_a, root.raw()));
            self.link_root(b.raw(), Id::new(to_b, root.raw()));
        }
        true
    }
    pub fn equivalent(&self, a: &Id, b: &Id) -> bool {
        self.find(a) == self.find(b)
    }
    fn nodes_in_class(&self, target: &Id, mode: MatchMode) -> SmallVec<[(&Node, Lift); 4]> {
        let target = self.find(target);
        let mut out = SmallVec::new();
        // The factor/limit tail below is deliberately written out in both
        // branches. Hoisting it into a shared closure measured ~2.5% slower on
        // AC10-hoapp and lambda-under; this is the hottest function here.
        if self.rev_valid || self.rev_tracked {
            for (node, edge) in self.rev.get(&target.raw()).into_iter().flatten() {
                let factors = factor_lifts(&target.lift(), edge);
                let limit = if mode == MatchMode::Canonical {
                    1
                } else {
                    factors.len()
                };
                for by in factors.into_iter().take(limit) {
                    out.push((node, by));
                }
            }
        } else {
            // Direct `ematch` is allowed on an unreconstructed graph. That
            // uncommon API path pays for a full scan rather than making every
            // ordinary union maintain the live reverse index.
            for (node, &raw) in &self.memo {
                let edge = self.find(&self.origin(raw));
                if edge.raw() != target.raw() {
                    continue;
                }
                let factors = factor_lifts(&target.lift(), &edge.lift());
                let limit = if mode == MatchMode::Canonical {
                    1
                } else {
                    factors.len()
                };
                for by in factors.into_iter().take(limit) {
                    out.push((node, by));
                }
            }
        }
        out
    }
    /// Substitute one ambient context variable. `target` lives in an n-variable
    /// context, while `replacement` and the result live in an (n-1)-variable
    /// context. Variables after `variable` shift down by one.
    pub fn substitute(&mut self, target: &Id, variable: usize, replacement: &Id) -> Id {
        assert_eq!(target.ctx(), replacement.ctx() + 1);
        assert!(variable < target.ctx());
        self.rebuild();
        let target = self.find_mut(target);
        let replacement = self.find_mut(replacement);

        // The lift is an exact dependency mask. If this context variable is
        // absent, substitution just deletes an unused context variable and no
        // e-class traversal is necessary.
        if let Some(projected) = target.remove_context_variable(variable) {
            return projected;
        }
        let output_ctx = replacement.ctx();
        let replacements: SmallVec<[Id; 8]> = (0..target.ctx())
            .map(|level| {
                if level == variable {
                    replacement
                } else {
                    let shifted = level - usize::from(level > variable);
                    self.var(output_ctx, shifted)
                }
            })
            .collect();
        let result = self.substitute_many(&target, output_ctx, &replacements);
        self.rebuild();
        self.find_mut(&result)
    }
    /// Simultaneously replace every context variable of `target` with an
    /// arbitrary term in `output_ctx`. Results are memoized to tie cycles.
    fn substitute_many(&mut self, target: &Id, output_ctx: usize, replacements: &[Id]) -> Id {
        assert_eq!(target.ctx(), replacements.len());
        assert!(
            replacements
                .iter()
                .all(|replacement| replacement.ctx() == output_ctx)
        );
        // A standalone caller may arrive outside a tracked rewrite batch.
        // Establish a clean index once, then keep it live for the traversal.
        if !self.rev_valid && !self.rev_tracked {
            self.rebuild();
        }
        self.rev_tracked = true;

        let mut memo = HashMap::default();
        let result = self.substitute_many_rec(target, output_ctx, replacements, &mut memo);
        self.find_mut(&result)
    }
    fn substitute_many_rec(
        &mut self,
        target: &Id,
        output_ctx: usize,
        replacements: &[Id],
        memo: &mut HashMap<(Id, SmallVec<[Id; 8]>), Id>,
    ) -> Id {
        let target = self.find_mut(target);
        assert_eq!(target.ctx(), replacements.len());
        let replacements: SmallVec<[Id; 8]> = replacements
            .iter()
            .map(|replacement| {
                assert_eq!(replacement.ctx(), output_ctx);
                self.find_mut(replacement)
            })
            .collect();
        let key = (target, replacements.clone());
        if let Some(result) = memo.get(&key) {
            return *result;
        }
        // As in single substitution, a cycle may return beneath extra unused
        // binders. Reuse its placeholder when both the source and replacement
        // prefix are merely lifted into the larger contexts.
        for ((old_target, old_replacements), old_result) in memo.iter() {
            if old_target.raw() == target.raw()
                && old_target.in_context(target.ctx()) == Some(target)
                && old_replacements.len() <= replacements.len()
                && old_replacements
                    .iter()
                    .zip(&replacements)
                    .all(|(old, new)| old.in_context(output_ctx) == Some(*new))
                && let Some(result) = old_result.in_context(output_ctx)
            {
                return result;
            }
        }

        let result = self.make_set(output_ctx);
        memo.insert(key, result);
        let nodes: Vec<_> = self
            .nodes_in_class(&target, MatchMode::Lifted)
            .into_iter()
            .map(|(node, by)| (node.clone(), by))
            .collect();
        for (node, by) in nodes {
            let translated = match node {
                Node::Var => {
                    debug_assert_eq!(by.dom(), 1);
                    let old_index = (0..by.cod()).find(|&index| by.get(index)).unwrap();
                    replacements[old_index]
                }
                Node::Atom(name) => self.atom_symbol(name, output_ctx),
                Node::App(function, argument) => {
                    let function = function.weaken(&by);
                    let argument = argument.weaken(&by);
                    let function =
                        self.substitute_many_rec(&function, output_ctx, &replacements, memo);
                    let argument =
                        self.substitute_many_rec(&argument, output_ctx, &replacements, memo);
                    self.app(function, argument)
                }
                Node::Binder(op, body) => {
                    let body = body.weaken(&by.append(true));
                    let mut under: SmallVec<[Id; 8]> = replacements
                        .iter()
                        .map(|replacement| replacement.in_context(output_ctx + 1).unwrap())
                        .collect();
                    under.push(self.var(output_ctx + 1, output_ctx));
                    let body = self.substitute_many_rec(&body, output_ctx + 1, &under, memo);
                    self.binder_symbol(op, body)
                }
            };
            self.union(&result, &translated);
        }
        self.find_mut(&result)
    }
    /// Extract a smallest term, counting every node as 1.
    pub fn extract(&mut self, target: &Id) -> Option<TermCtx> {
        self.extract_with(target, |_| 1)
    }
    /// Extract the term of least total weight, where a term's weight is the
    /// sum of `weight` over its nodes.
    ///
    /// A per-node weight rather than a whole-term cost is what keeps this
    /// linear: each e-class is costed once, instead of re-walking every
    /// candidate subtree at every level. It also makes the cost monotone by
    /// construction, since wrapping a term only adds a node.
    pub fn extract_with(&mut self, target: &Id, weight: impl Fn(Head) -> u64) -> Option<TermCtx> {
        self.rebuild();
        let target = self.find(target);
        let scope = target.ctx();
        let mut choices = HashMap::default();
        self.choose(
            &target,
            scope,
            &mut choices,
            &mut HashSet::default(),
            &weight,
        )?;
        Some(TermCtx {
            scope,
            t: self.build(&target, scope, &choices),
        })
    }
    /// Pick the cheapest e-node for `target` and, recursively, for every class
    /// it reaches; record the winner and its total weight. Returns `None` for
    /// a class with no finite term.
    fn choose(
        &self,
        target: &Id,
        root_scope: usize,
        choices: &mut HashMap<Id, Option<(u64, Node, Lift)>>,
        active_raw: &mut HashSet<RawId>,
        weight: &impl Fn(Head) -> u64,
    ) -> Option<u64> {
        let target = self.find(target);
        if let Some(choice) = choices.get(&target) {
            return choice.as_ref().map(|(cost, _, _)| *cost);
        }
        // A recursive class can return at a different lifted placement on
        // every trip through a binder. The fat IDs then differ even though
        // the underlying class cycle is the same, so track active raw IDs as
        // well as memoizing complete results by fat ID.
        if !active_raw.insert(target.raw()) {
            return None;
        }

        // Mark this fat ID as being visited. Recursive enodes that return to
        // it are skipped, while other finite representatives remain usable.
        choices.insert(target, None);
        let mut best: Option<(u64, Node, Lift)> = None;
        for (node, by) in self.nodes_in_class(&target, MatchMode::Lifted) {
            let mut total = match node {
                Node::Var => {
                    if var_term(&by, target.ctx(), root_scope).is_none() {
                        continue;
                    }
                    weight(Head::Var)
                }
                Node::Atom(name) => weight(Head::Atom(*name)),
                Node::App(_, _) => weight(Head::App),
                Node::Binder(op, _) => weight(Head::Binder(*op)),
            };
            let mut finite = true;
            for child in node_children(node, &by) {
                let Some(cost) = self.choose(&child, root_scope, choices, active_raw, weight)
                else {
                    finite = false;
                    break;
                };
                total = total.saturating_add(cost);
            }
            if finite && best.as_ref().is_none_or(|(best, _, _)| total < *best) {
                best = Some((total, node.clone(), by));
            }
        }
        active_raw.remove(&target.raw());
        let cost = best.as_ref().map(|(cost, _, _)| *cost);
        choices.insert(target, best);
        cost
    }
    /// Materialize the term from the winners `choose` recorded. The chosen
    /// nodes form a DAG, so this costs one step per node of the output.
    fn build(
        &self,
        target: &Id,
        root_scope: usize,
        choices: &HashMap<Id, Option<(u64, Node, Lift)>>,
    ) -> Term {
        let target = self.find(target);
        let (_, node, by) = choices
            .get(&target)
            .and_then(Option::as_ref)
            .expect("choose recorded a finite winner for every reachable class");
        let mut children =
            node_children(node, by).map(|child| self.build(&child, root_scope, choices));
        match node {
            Node::Var => var_term(by, target.ctx(), root_scope).expect("checked by choose"),
            Node::Atom(name) => Term::Atom(*name),
            Node::App(_, _) => {
                let function = children.next().expect("App has two children");
                let argument = children.next().expect("App has two children");
                Term::App(Box::new(function), Box::new(argument))
            }
            Node::Binder(op, _) => {
                Term::Binder(*op, Box::new(children.next().expect("Binder has a body")))
            }
        }
    }
    fn reindex(&mut self) {
        self.rev.clear();
        for (node, &raw) in &self.memo {
            let edge = self.find(&self.origin(raw));
            self.rev
                .entry(edge.raw())
                .or_default()
                .push((node.clone(), edge.lift()));
        }
        self.rev.sort_keys();
        self.rev_tracked = true;
        self.rev_valid = true;
    }
    /// Instantiate a binding stored in `top context + canonical formals`.
    /// Its fat-ID lift records which formal arguments it actually uses.
    fn instantiate_binding(
        &mut self,
        binding: &Id,
        top_ctx: usize,
        current_ctx: usize,
        arguments: &[Id],
    ) -> Option<Id> {
        if binding.ctx() != top_ctx + arguments.len()
            || arguments
                .iter()
                .any(|argument| argument.ctx() != current_ctx)
        {
            return None;
        }
        let mut replacements: SmallVec<[Id; 8]> = (0..top_ctx)
            .map(|level| self.var(current_ctx, level))
            .collect();
        replacements.extend(arguments.iter().copied());
        Some(self.substitute_many(binding, current_ctx, &replacements))
    }
    fn ematch_rec(
        &self,
        pattern: &Pattern,
        target: &Id,
        subst: Subst,
        mode: MatchMode,
        top_ctx: usize,
        out: &mut MatchResults,
    ) {
        match pattern {
            Pattern::MetaVar(name, arguments) => {
                let Some(occurrence) = pattern_occurrence_lift(top_ctx, target.ctx(), arguments)
                else {
                    return;
                };
                match subst.get(name).cloned() {
                    Some(previous) if self.equivalent(&previous.weaken(&occurrence), target) => {
                        out.push(subst);
                    }
                    Some(_) => {}
                    None => {
                        let target = self.find(target);
                        let Some(binding_lift) = occurrence.factor(&target.lift()) else {
                            return;
                        };
                        let mut next = subst;
                        next.insert(*name, Id::new(binding_lift, target.raw()));
                        out.push(next);
                    }
                }
            }
            Pattern::FVar(index) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    if matches!(node, Node::Var)
                        && index.get() < top_ctx
                        && by == Lift::select(target.ctx(), index.get())
                    {
                        out.push(subst.clone());
                    }
                }
            }
            Pattern::BVar(index) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    let depth = target.ctx() - top_ctx;
                    if matches!(node, Node::Var)
                        && index.get() < depth
                        && by == Lift::select(target.ctx(), target.ctx() - 1 - index.get())
                    {
                        out.push(subst.clone());
                    }
                }
            }
            Pattern::Atom(name) => {
                for (node, _) in self.nodes_in_class(target, mode) {
                    if matches!(node, Node::Atom(symbol) if symbol == name) {
                        out.push(subst.clone());
                    }
                }
            }
            Pattern::App(function_pattern, argument_pattern) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    let Node::App(function, argument) = node else {
                        continue;
                    };
                    let function = function.weaken(&by);
                    let argument = argument.weaken(&by);
                    let mut functions = MatchResults::new();
                    self.ematch_rec(
                        function_pattern,
                        &function,
                        subst.clone(),
                        mode,
                        top_ctx,
                        &mut functions,
                    );
                    for function_subst in functions {
                        self.ematch_rec(
                            argument_pattern,
                            &argument,
                            function_subst,
                            mode,
                            top_ctx,
                            out,
                        );
                    }
                }
            }
            Pattern::Binder(op, body_pattern) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    let Node::Binder(node_op, body) = node else {
                        continue;
                    };
                    if node_op != op {
                        continue;
                    }
                    let lifted = body.weaken(&by.append(true));
                    self.ematch_rec(body_pattern, &lifted, subst.clone(), mode, top_ctx, out);
                }
            }
            // `#subst` computes a term during RHS instantiation; it is not an
            // e-node and therefore cannot match anything on a left-hand side.
            Pattern::Subst(_, _) => {}
        }
    }
    pub fn ematch(&self, pattern: &Pattern, target: &Id) -> Vec<Subst> {
        if pattern.match_metavariables().is_err() {
            return vec![];
        }
        self.ematch_with(pattern, target, MatchMode::Canonical)
            .into_vec()
    }
    fn ematch_with(&self, pattern: &Pattern, target: &Id, mode: MatchMode) -> MatchResults {
        let mut matches = MatchResults::new();
        self.ematch_rec(
            pattern,
            target,
            Subst::default(),
            mode,
            target.ctx(),
            &mut matches,
        );
        matches
    }
    pub fn ematch_lifted(&self, pattern: &Pattern, target: &Id) -> Vec<Subst> {
        if pattern.match_metavariables().is_err() {
            return vec![];
        }
        self.ematch_with(pattern, target, MatchMode::Lifted)
            .into_vec()
    }
    /// Match a pattern against every canonical e-class placement.
    pub fn search(&mut self, pattern: &Pattern) -> Vec<(usize, Subst)> {
        self.rebuild();
        if pattern.match_metavariables().is_err() {
            return vec![];
        }
        let targets = self.canonical_targets();
        let mut matches = vec![];
        for target in targets {
            let context = target.ctx();
            matches.extend(
                self.ematch_with(pattern, &target, MatchMode::Canonical)
                    .into_iter()
                    .map(|subst| (context, subst)),
            );
        }
        matches
    }
    pub fn try_instantiate(&mut self, pattern: &Pattern, ctx: usize, subst: &Subst) -> Option<Id> {
        self.try_instantiate_rec(pattern, ctx, ctx, subst)
    }
    fn try_instantiate_rec(
        &mut self,
        pattern: &Pattern,
        ctx: usize,
        top_ctx: usize,
        subst: &Subst,
    ) -> Option<Id> {
        match pattern {
            Pattern::MetaVar(name, arguments) => {
                let binding = *subst.get(name)?;
                if let Some(occurrence) = pattern_occurrence_lift(top_ctx, ctx, arguments) {
                    return Some(binding.weaken(&occurrence));
                }
                let arguments: Option<SmallVec<[Id; 2]>> = arguments
                    .iter()
                    .map(|argument| self.try_instantiate_rec(argument, ctx, top_ctx, subst))
                    .collect();
                self.instantiate_binding(&binding, top_ctx, ctx, &arguments?)
            }
            Pattern::FVar(index) => (index.get() < top_ctx).then(|| self.var(ctx, index.get())),
            Pattern::BVar(index) => {
                let depth = ctx.checked_sub(top_ctx)?;
                (index.get() < depth).then(|| self.var(ctx, ctx - 1 - index.get()))
            }
            Pattern::Atom(name) => Some(self.atom_symbol(*name, ctx)),
            Pattern::App(function, argument) => {
                let function = self.try_instantiate_rec(function, ctx, top_ctx, subst)?;
                let argument = self.try_instantiate_rec(argument, ctx, top_ctx, subst)?;
                Some(self.app(function, argument))
            }
            Pattern::Binder(op, body) => {
                let body = self.try_instantiate_rec(body, ctx + 1, top_ctx, subst)?;
                Some(self.binder_symbol(*op, body))
            }
            Pattern::Subst(body, replacement) => {
                let body = self.try_instantiate_rec(body, ctx + 1, top_ctx, subst)?;
                let replacement = self.try_instantiate_rec(replacement, ctx, top_ctx, subst)?;
                Some(self.substitute(&body, ctx, &replacement))
            }
        }
    }
    fn canonical_targets(&self) -> Vec<Id> {
        let mut targets = HashSet::default();
        for &raw in self.memo.values() {
            targets.insert(self.find(&self.origin(raw)));
        }
        let mut targets: Vec<_> = targets.into_iter().collect();
        targets.sort_by_key(|id| (id.raw(), id.lift().cod(), id.lift().selected_bits()));
        targets
    }
    pub fn saturate(&mut self, rules: &[Rewrite]) -> RunStats {
        self.run(rules, usize::MAX)
    }
    pub fn run(&mut self, rules: &[Rewrite], limit: usize) -> RunStats {
        let mut stats = RunStats::default();
        let rebuild_before = self.rebuild_time_total;
        self.rebuild();
        stats.rebuild_time += self.rebuild_time_total - rebuild_before;
        // Saturation usually grows the match set, so retain each rule's
        // allocation across rounds while preserving search-then-apply.
        let mut matches_by_rule: Vec<Vec<(Id, Subst)>> = vec![Vec::new(); rules.len()];
        while stats.rounds < limit {
            let before_nodes = self.memo.len();

            let start = Instant::now();
            let targets = self.canonical_targets();
            for (rule, matches) in rules.iter().zip(&mut matches_by_rule) {
                matches.clear();
                for target in &targets {
                    for subst in self.ematch_with(rule.lhs(), target, MatchMode::Canonical) {
                        matches.push((*target, subst));
                    }
                }
            }
            stats.match_time += start.elapsed();
            let start = Instant::now();
            let rebuild_before = self.rebuild_time_total;
            self.rev_tracked = rules.iter().any(|rule| rule.rhs_needs_traversal);
            let mut changed = false;
            for (rule, matches) in rules.iter().zip(&mut matches_by_rule) {
                for (target, subst) in matches.drain(..) {
                    if let Some(replacement) =
                        self.try_instantiate(rule.rhs(), target.ctx(), &subst)
                    {
                        let unioned = self.union(&target, &replacement);
                        stats.unions += usize::from(unioned);
                        changed |= unioned;
                    }
                }
            }
            let elapsed = start.elapsed();
            let nested_rebuild = self.rebuild_time_total - rebuild_before;
            stats.rebuild_time += nested_rebuild;
            stats.apply_time += elapsed.saturating_sub(nested_rebuild);

            let rebuild_before = self.rebuild_time_total;
            let rebuilt = self.rebuild();
            stats.rebuild_time += self.rebuild_time_total - rebuild_before;
            changed |= rebuilt;
            changed |= before_nodes != self.memo.len();
            if !changed {
                return stats;
            }
            stats.rounds += 1;
        }
        stats
    }
    pub fn class_count(&self) -> usize {
        (0..self.parent.len() as RawId)
            .filter(|&raw| self.parent[raw as usize].raw() == raw)
            .count()
    }
    pub fn node_count(&self) -> usize {
        self.memo.len()
    }
    pub fn raw_id_count(&self) -> usize {
        self.parent.len()
    }
    /// Deterministic, low-level view of every e-class. Each enode is shown
    /// with the lift that embeds its own context into the class context.
    pub fn dump(&mut self) -> String {
        fn node_text(node: &Node) -> String {
            fn symbol_text(symbol: Symbol) -> String {
                Term::Atom(symbol).to_string()
            }
            match node {
                Node::Var => "var".into(),
                Node::Atom(name) => symbol_text(*name),
                Node::App(function, argument) => {
                    format!("({} {})", function.show(), argument.show())
                }
                Node::Binder(op, body) => format!("(@{} {})", symbol_text(*op), body.show()),
            }
        }

        self.rebuild();
        let classes: Vec<_> = (0..self.parent.len() as RawId)
            .filter(|&raw| self.parent[raw as usize].raw() == raw)
            .map(|raw| {
                (
                    raw,
                    self.parent[raw as usize].ctx(),
                    self.rev.get(&raw).cloned().unwrap_or_default(),
                )
            })
            .collect();
        let mut lines = vec![format!(
            "egraph: {} classes, {} e-nodes",
            classes.len(),
            self.memo.len()
        )];
        for (raw, ctx, nodes) in classes {
            let id = Id::new(Lift::identity(ctx), raw);
            let representative = self
                .extract(&id)
                .map_or_else(|| "<recursive>".into(), |term| term.display().to_string());
            lines.push(format!("e{raw} = ctx{ctx} |-> {representative}"));
            for (node, lift) in nodes {
                lines.push(format!(
                    "  {} <- {}",
                    Id::new(lift, raw).show(),
                    node_text(&node)
                ));
            }
        }
        lines.join("\n")
    }
    pub fn rebuild(&mut self) -> bool {
        let start = Instant::now();
        let changed = self.rebuild_inner();
        self.rebuild_time_total += start.elapsed();
        changed
    }
    fn rebuild_inner(&mut self) -> bool {
        if self.rev_valid {
            return false;
        }
        let mut any_changed = false;
        loop {
            let nodes = std::mem::take(&mut self.memo);
            let mut changed = false;
            for (node, raw) in nodes {
                let raw_scope = self.parent[raw as usize].ctx();
                let old = Id::new(Lift::identity(raw_scope), raw);
                let (lift, canonical) = self.canonical_node(&node);
                if lift != Lift::identity(raw_scope) || canonical != node {
                    any_changed = true;
                }
                let base = if let Some(&existing) = self.memo.get(&canonical) {
                    self.find_mut(&Id::new(Lift::identity(lift.dom()), existing))
                } else if lift == Lift::identity(raw_scope) {
                    self.memo.insert(canonical, raw);
                    old
                } else {
                    let fresh = self.make_set(lift.dom());
                    self.memo.insert(canonical, fresh.raw());
                    fresh
                };
                changed |= self.union(&old, &base.weaken(&lift));
            }
            any_changed |= changed;
            if !changed {
                self.reindex();
                return any_changed;
            }
        }
    }
}
