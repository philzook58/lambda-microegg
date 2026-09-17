use indexmap::IndexMap;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;
use symbol_table::GlobalSymbol as Symbol;

pub type RawId = u32;

/// An order-preserving injection from an intrinsic dependency context into
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Pullback {
    lift: Lift,
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
    /// `self.compose(from_left) == lift` and
    /// `other.compose(from_right) == lift`.
    fn pullback(&self, other: &Self) -> Pullback {
        assert_eq!(self.cod(), other.cod());
        let pullback = Self::from_bits(self.selected_bits() & other.selected_bits(), self.cod());
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
            lift: pullback,
            from_left: Self::from_bits(left, a),
            from_right: Self::from_bits(right, b),
        }
    }
    /// Largest subcontext of their shared domain on which the two lifts agree
    /// coordinate by coordinate.
    fn equalizer(&self, other: &Self) -> Self {
        assert_eq!(self.cod(), other.cod());
        assert_eq!(self.dom(), other.dom());
        let left: Vec<_> = (0..self.cod()).filter(|&i| self.get(i)).collect();
        let right: Vec<_> = (0..other.cod()).filter(|&i| other.get(i)).collect();
        let bits = left
            .iter()
            .zip(right)
            .enumerate()
            .fold(0, |bits, (i, (left, right))| {
                bits | (u8::from(*left == right) << i)
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
    fn remove_coord(&self, index: usize) -> Option<Self> {
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
    App(Symbol, Vec<Id>),
    Lam(Id),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    /// A Miller metavariable allowed to use distinct pattern-local binders.
    /// The numbers are de Bruijn indices: 0 is the nearest enclosing lambda.
    /// Top-level coordinates are implicit and always available.
    Var(Symbol, Vec<usize>),
    /// An absolute coordinate in the context outside the pattern.
    Coord(usize),
    /// A de Bruijn index into the named lambdas introduced by this pattern.
    Bound(usize),
    Atom(Symbol),
    App(Symbol, Vec<Pattern>),
    Lam(Box<Pattern>),
    /// Built-in capture-avoiding substitution. Its body is parsed beneath
    /// one additional binder and the result lives outside that binder.
    Subst(Box<Pattern>, Box<Pattern>),
}

impl Pattern {
    pub fn var(name: &str) -> Self {
        Self::Var(name.into(), vec![])
    }
    pub fn miller(name: &str, bound: Vec<usize>) -> Self {
        Self::Var(name.into(), bound)
    }
    pub fn atom(name: &str) -> Self {
        Self::Atom(name.into())
    }
    pub fn app(op: &str, children: Vec<Self>) -> Self {
        Self::App(op.into(), children)
    }

    /// Whether instantiating this pattern may need to traverse an e-class to
    /// permute Miller arguments. Ordered argument lists remain a packed lift.
    fn may_permute(&self, depth: usize) -> bool {
        match self {
            Self::Var(_, bound) => {
                if bound.iter().any(|&index| index >= depth) {
                    return false;
                }
                bound
                    .iter()
                    .map(|index| depth - 1 - index)
                    .collect::<SmallVec<[usize; 4]>>()
                    .windows(2)
                    .any(|pair| pair[0] >= pair[1])
            }
            Self::App(_, children) => children.iter().any(|child| child.may_permute(depth)),
            Self::Lam(body) => body.may_permute(depth + 1),
            Self::Subst(body, replacement) => {
                body.may_permute(depth + 1) || replacement.may_permute(depth)
            }
            Self::Coord(_) | Self::Bound(_) | Self::Atom(_) => false,
        }
    }

    /// Reject nonlinear Miller occurrences that apply the same metavariable
    /// with different permutations of the surrounding binders. Those would
    /// require constructing a permuted term merely to decide a match.
    pub fn validate_match_pattern(&self) -> Result<(), String> {
        fn go(
            pattern: &Pattern,
            depth: usize,
            orders: &mut HashMap<Symbol, Vec<usize>>,
        ) -> Result<(), String> {
            match pattern {
                Pattern::Var(name, bound) => {
                    if bound.iter().any(|&index| index >= depth) {
                        return Err(format!(
                            "Miller metavariable '{name}' refers outside the pattern binders"
                        ));
                    }
                    if bound
                        .iter()
                        .enumerate()
                        .any(|(i, index)| bound[..i].contains(index))
                    {
                        return Err(format!(
                            "Miller metavariable '{name}' repeats a pattern binder"
                        ));
                    }

                    // The e-graph context is ordered. Record the order in
                    // which the written formal arguments occur in that
                    // context, independent of their particular binder names.
                    let mut order: Vec<_> = (0..bound.len()).collect();
                    order.sort_unstable_by_key(|&formal| depth - 1 - bound[formal]);
                    if let Some(previous) = orders.get(name) {
                        if previous.len() != order.len() {
                            return Err(format!(
                                "Miller metavariable '{name}' has inconsistent arity in match pattern"
                            ));
                        }
                        if previous != &order {
                            return Err(format!(
                                "twisted nonlinear Miller metavariable '{name}' uses different binder orders"
                            ));
                        }
                    } else {
                        orders.insert(*name, order);
                    }
                    Ok(())
                }
                Pattern::App(_, children) => {
                    for child in children {
                        go(child, depth, orders)?;
                    }
                    Ok(())
                }
                Pattern::Lam(body) => go(body, depth + 1, orders),
                Pattern::Subst(body, replacement) => {
                    go(body, depth + 1, orders)?;
                    go(replacement, depth, orders)
                }
                Pattern::Coord(_) | Pattern::Bound(_) | Pattern::Atom(_) => Ok(()),
            }
        }

        go(self, 0, &mut HashMap::default())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Var(usize),
    Atom(Symbol),
    App(Symbol, Vec<Term>),
    Lam(Box<Term>),
}

impl Term {
    pub fn size(&self) -> usize {
        match self {
            Self::Var(_) | Self::Atom(_) => 1,
            Self::App(_, children) => 1 + children.iter().map(Self::size).sum::<usize>(),
            Self::Lam(body) => 1 + body.size(),
        }
    }
}

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn atom(f: &mut std::fmt::Formatter<'_>, text: &str) -> std::fmt::Result {
            let bare = !text.is_empty()
                && !text.starts_with(['?', '$'])
                && !text
                    .chars()
                    .any(|c| c.is_whitespace() || matches!(c, '(' | ')' | ';' | '"'));
            if bare {
                return f.write_str(text);
            }
            f.write_str("\"")?;
            for c in text.chars() {
                match c {
                    '\n' => f.write_str("\\n")?,
                    '\t' => f.write_str("\\t")?,
                    '"' | '\\' => write!(f, "\\{c}")?,
                    c => write!(f, "{c}")?,
                }
            }
            f.write_str("\"")
        }
        match self {
            Self::Var(index) => write!(f, "${index}"),
            Self::Atom(name) => atom(f, name.as_str()),
            Self::App(op, children) => {
                f.write_str("(")?;
                atom(f, op.as_str())?;
                for child in children {
                    write!(f, " {child}")?;
                }
                f.write_str(")")
            }
            Self::Lam(body) => write!(f, "(lam {body})"),
        }
    }
}

pub struct NamedTerm<'a> {
    term: &'a Term,
    outer_ctx: usize,
    root_binders: &'a [String],
}

impl std::fmt::Display for NamedTerm<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn atom(
            f: &mut std::fmt::Formatter<'_>,
            text: &str,
            force_quote: bool,
        ) -> std::fmt::Result {
            let bare = !force_quote
                && !text.is_empty()
                && !text.starts_with(['?', '$'])
                && !text
                    .chars()
                    .any(|c| c.is_whitespace() || matches!(c, '(' | ')' | ';' | '"'));
            if bare {
                return f.write_str(text);
            }
            f.write_str("\"")?;
            for c in text.chars() {
                match c {
                    '\n' => f.write_str("\\n")?,
                    '\t' => f.write_str("\\t")?,
                    '"' | '\\' => write!(f, "\\{c}")?,
                    c => write!(f, "{c}")?,
                }
            }
            f.write_str("\"")
        }
        fn collides(text: &str, root_binders: &[String], binders: &[String]) -> bool {
            let base = text
                .rsplit_once('@')
                .filter(|(_, suffix)| suffix.parse::<usize>().is_ok())
                .map_or(text, |(base, _)| base);
            root_binders
                .iter()
                .chain(binders)
                .any(|binder| binder == base)
        }
        fn go(
            term: &Term,
            f: &mut std::fmt::Formatter<'_>,
            outer_ctx: usize,
            root_binders: &[String],
            binders: &mut Vec<String>,
        ) -> std::fmt::Result {
            let root_ctx = outer_ctx + root_binders.len();
            match term {
                Term::Var(level) if *level < outer_ctx => write!(f, "${level}"),
                Term::Var(level) if *level < root_ctx => {
                    f.write_str(&root_binders[level - outer_ctx])
                }
                Term::Var(level) => match binders.get(level - root_ctx) {
                    Some(name) => f.write_str(name),
                    None => write!(f, "${level}"),
                },
                Term::Atom(name) => atom(
                    f,
                    name.as_str(),
                    collides(name.as_str(), root_binders, binders),
                ),
                Term::App(op, children) => {
                    f.write_str("(")?;
                    atom(f, op.as_str(), false)?;
                    for child in children {
                        f.write_str(" ")?;
                        go(child, f, outer_ctx, root_binders, binders)?;
                    }
                    f.write_str(")")
                }
                Term::Lam(body) => {
                    let name = format!("x{}", root_binders.len() + binders.len());
                    write!(f, "(lam {name} ")?;
                    binders.push(name);
                    go(body, f, outer_ctx, root_binders, binders)?;
                    binders.pop();
                    f.write_str(")")
                }
            }
        }
        go(self.term, f, self.outer_ctx, self.root_binders, &mut vec![])
    }
}

impl Term {
    /// Render a term using generated names for binders. Variables in the
    /// context outside the term remain `$0`, `$1`, and so on.
    pub fn display_in(&self, outer_ctx: usize) -> NamedTerm<'_> {
        self.display_with_root_binders(outer_ctx, &[])
    }

    /// As above, but the final root coordinates are named formal parameters.
    /// This is used to render Miller substitutions without exposing levels.
    pub fn display_with_root_binders<'a>(
        &'a self,
        outer_ctx: usize,
        root_binders: &'a [String],
    ) -> NamedTerm<'a> {
        NamedTerm {
            term: self,
            outer_ctx,
            root_binders,
        }
    }
}

/// A matcher-level abstraction. `body` uses the pattern's top context followed
/// by the parameters it actually mentions, in the e-graph's ordered context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MLam {
    body: Id,
    /// Three bits each for the kept count, arity, and up to seven formal
    /// indices. This is the only match-dependent data beyond `body`: it says
    /// which permitted Miller arguments the matched term actually used.
    shape: u32,
}

impl MLam {
    fn new(top_ctx: usize, arity: usize, kept: &[usize], body: Id) -> Self {
        debug_assert!(arity <= 7 && kept.len() <= 7);
        debug_assert!(kept.iter().all(|&formal| formal < arity));
        debug_assert_eq!(body.ctx(), top_ctx + kept.len());
        let mut shape = kept.len() as u32 | (arity as u32) << 3;
        for (index, &formal) in kept.iter().enumerate() {
            shape |= (formal as u32) << (6 + 3 * index);
        }
        Self { body, shape }
    }
    fn kept_len(&self) -> usize {
        (self.shape & 0b111) as usize
    }
    fn kept_indices(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.kept_len()).map(|index| ((self.shape >> (6 + 3 * index)) & 0b111) as usize)
    }
    pub fn top_ctx(&self) -> usize {
        self.body.ctx() - self.kept_len()
    }
    pub fn arity(&self) -> usize {
        ((self.shape >> 3) & 0b111) as usize
    }
    pub fn kept(&self) -> SmallVec<[usize; 4]> {
        self.kept_indices().collect()
    }
    pub fn body(&self) -> Id {
        self.body
    }
}

#[derive(Clone, Default)]
pub struct Subst(SmallVec<[(Symbol, MLam); 4]>);

impl Subst {
    fn get(&self, name: &Symbol) -> Option<&MLam> {
        self.0
            .iter()
            .find_map(|(key, binding)| (*key == *name).then_some(binding))
    }
    fn insert(&mut self, name: Symbol, binding: MLam) {
        self.0.push((name, binding));
    }
    pub fn bindings(&self) -> impl Iterator<Item = (&str, &MLam)> + '_ {
        self.0
            .iter()
            .map(|(name, binding)| (name.as_str(), binding))
    }
}

impl std::ops::Index<&str> for Subst {
    type Output = MLam;
    fn index(&self, name: &str) -> &MLam {
        self.get(&name.into()).expect("unbound pattern variable")
    }
}

/// Find all W such that W.compose(edge) = target. A redundant edge may
/// admit several W, corresponding to different variables in the target.
fn factor_lifts(target: &Lift, edge: &Lift) -> Vec<Lift> {
    if target.dom() != edge.dom() || edge.cod() > target.cod() {
        return vec![];
    }
    if edge.is_identity() {
        return vec![*target];
    }
    fn visit(
        target: &Lift,
        edge: &Lift,
        source: usize,
        next: usize,
        chosen: &mut Vec<usize>,
        out: &mut Vec<Lift>,
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
    let mut out = vec![];
    visit(target, edge, 0, 0, &mut vec![], &mut out);
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

#[derive(Default)]
pub struct EGraph {
    parent: Vec<Id>,
    scope: Vec<usize>,
    memo: IndexMap<Node, RawId, rustc_hash::FxBuildHasher>,
    rev: IndexMap<RawId, Vec<(Node, Lift)>, rustc_hash::FxBuildHasher>,
    /// Keep `rev` usable between construction and the batch's final rebuild
    /// when a constructive Miller permutation needs class-local traversal.
    rev_tracked: bool,
    rev_valid: bool,
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
        self.scope.push(scope);
        id
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
        let edge = self.parent[id.raw() as usize];
        if edge.raw() == id.raw() {
            return *id;
        }
        let root = self.find_mut(&edge);
        self.parent[id.raw() as usize] = root;
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
        let base = self.intern(0, Node::Atom(name.into()));
        base.weaken(&Lift::unused(ctx))
    }
    pub fn app(&mut self, op: &str, children: Vec<Id>) -> Id {
        assert!(!children.is_empty());
        let ctx = children[0].ctx();
        assert!(children.iter().all(|c| c.ctx() == ctx));
        let (common, node) = self.canonical_node(&Node::App(op.into(), children));
        let base = self.intern(common.dom(), node);
        base.weaken(&common)
    }
    /// The bound variable is the final coordinate of the body's context.
    pub fn lam(&mut self, body: Id) -> Id {
        assert!(body.ctx() > 0);
        let (outer, node) = self.canonical_node(&Node::Lam(body));
        let base = self.intern(outer.dom(), node);
        base.weaken(&outer)
    }
    /// Return the pulled e-node and the lift back to its original context.
    fn canonical_node(&mut self, node: &Node) -> (Lift, Node) {
        match node {
            Node::Var => (Lift::identity(1), Node::Var),
            Node::Atom(s) => (Lift::identity(0), Node::Atom(*s)),
            Node::App(op, children) => {
                let children: Vec<_> = children.iter().map(|c| self.find_mut(c)).collect();
                if children.iter().all(|c| c.lift().is_identity()) {
                    return (Lift::identity(children[0].ctx()), Node::App(*op, children));
                }
                let common = children
                    .iter()
                    .skip(1)
                    .fold(children[0].lift(), |t, c| t.union(&c.lift()).lift);
                let narrowed = children
                    .into_iter()
                    .map(|c| {
                        let projection = common.union(&c.lift()).right;
                        Id::new(projection, c.raw())
                    })
                    .collect();
                (common, Node::App(*op, narrowed))
            }
            Node::Lam(body) => {
                let body = self.find_mut(body);
                let outer = body.lift().prefix(body.ctx() - 1);
                let core_body = Id::new(
                    Lift::identity(outer.dom()).append(body.lift().get(body.ctx() - 1)),
                    body.raw(),
                );
                (outer, Node::Lam(core_body))
            }
        }
    }
    /// Link two union-find roots, updating the reverse e-class index when a
    /// constructive rewrite has requested it. Congruence may still be dirty,
    /// but class-local traversals then remain cheap until the next rebuild.
    fn link_root(&mut self, child: RawId, parent: Id) {
        debug_assert_eq!(self.parent[child as usize].raw(), child);
        debug_assert_ne!(child, parent.raw());
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
            // the coordinates on which the placements agree. For example,
            // f(x) = f(y) turns the result of f into a context-independent
            // value rather than treating x and y themselves as equal.
            let dependency = a.lift().equalizer(&b.lift());
            let root = self.make_set(dependency.dom());
            self.link_root(a.raw(), Id::new(dependency, root.raw()));
            return true;
        }
        let Pullback {
            lift: common,
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
    fn nodes_in_class(&self, target: &Id, mode: MatchMode) -> Vec<(&Node, Lift)> {
        let target = self.find(target);
        let mut out = vec![];
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
                let origin = Id::new(Lift::identity(self.scope[raw as usize]), raw);
                let edge = self.find(&origin);
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
    /// Substitute one ambient coordinate. `target` lives in an n-variable
    /// context, while `replacement` and the result live in an (n-1)-variable
    /// context. Coordinates after `variable` shift down by one.
    pub fn substitute(&mut self, target: &Id, variable: usize, replacement: &Id) -> Id {
        assert_eq!(target.ctx(), replacement.ctx() + 1);
        assert!(variable < target.ctx());
        self.rebuild();
        let mut memo = HashMap::default();
        let result = self.substitute_rec(target, variable, replacement, &mut memo);
        self.rebuild();
        self.find_mut(&result)
    }
    fn substitute_rec(
        &mut self,
        target: &Id,
        variable: usize,
        replacement: &Id,
        memo: &mut HashMap<(Id, usize, Id), Id>,
    ) -> Id {
        let target = self.find_mut(target);
        let replacement = self.find_mut(replacement);
        assert_eq!(target.ctx(), replacement.ctx() + 1);

        // The lift is an exact dependency mask. If this coordinate is
        // absent, substitution is just deletion of an unused input and no
        // e-class traversal is necessary.
        if let Some(projected) = target.remove_coord(variable) {
            return projected;
        }

        let key = (target, variable, replacement);
        if let Some(result) = memo.get(&key) {
            return *result;
        }
        // Binder traversal can revisit the same raw cycle with extra unused
        // trailing coordinates. Reuse the earlier placeholder after changing
        // only its ambient context, rather than missing the cycle because the
        // full fat IDs differ.
        for ((old_target, old_variable, old_replacement), old_result) in memo.iter() {
            if *old_variable == variable
                && old_target.raw() == target.raw()
                && old_replacement.raw() == replacement.raw()
                && old_target.in_context(target.ctx()) == Some(target)
                && old_replacement.in_context(replacement.ctx()) == Some(replacement)
                && let Some(result) = old_result.in_context(target.ctx() - 1)
            {
                return result;
            }
        }

        // Install the result before following children. An e-class can be
        // cyclic (for example after x = f(x)), so recursive visits must see
        // a result to tie the translated cycle back to.
        let result = self.make_set(target.ctx() - 1);
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
                    let old_index = (0..by.cod()).find(|&i| by.get(i)).unwrap();
                    if old_index == variable {
                        replacement
                    } else {
                        let new_index = old_index - usize::from(old_index > variable);
                        self.var(target.ctx() - 1, new_index)
                    }
                }
                Node::Atom(name) => self.atom(name.as_str(), target.ctx() - 1),
                Node::App(op, children) => {
                    let children = children
                        .into_iter()
                        .map(|child| {
                            let child = child.weaken(&by);
                            self.substitute_rec(&child, variable, &replacement, memo)
                        })
                        .collect();
                    self.app(op.as_str(), children)
                }
                Node::Lam(body) => {
                    let body = body.weaken(&by.append(true));
                    let replacement_under_binder = replacement.in_context(target.ctx()).unwrap();
                    let body =
                        self.substitute_rec(&body, variable, &replacement_under_binder, memo);
                    self.lam(body)
                }
            };
            self.union(&result, &translated);
        }
        self.find_mut(&result)
    }
    /// Rename all coordinates of `target` at once. Ordered injections stay a
    /// single lift; permutations fall back to a memoized e-graph traversal.
    fn remap_variables(&mut self, target: &Id, output_ctx: usize, coordinates: &[usize]) -> Id {
        assert_eq!(target.ctx(), coordinates.len());
        assert!(coordinates.iter().all(|&index| index < output_ctx));
        if coordinates.windows(2).all(|pair| pair[0] < pair[1]) {
            return target.weaken(&Lift::selected(output_ctx, coordinates));
        }

        // A standalone caller may arrive outside a tracked rewrite batch.
        // Establish a clean index once, then keep it live for the traversal.
        if !self.rev_valid && !self.rev_tracked {
            self.rebuild();
        }
        self.rev_tracked = true;

        // Rebuilding is amortized over the surrounding rewrite round. The
        // reverse class index is maintained across these unions, so recursive
        // construction can still inspect only the source e-class.
        let replacements: SmallVec<[Id; 8]> = coordinates
            .iter()
            .map(|&index| self.var(output_ctx, index))
            .collect();
        let mut memo = HashMap::default();
        let result = self.remap_variables_rec(target, output_ctx, &replacements, &mut memo);
        self.find_mut(&result)
    }
    fn remap_variables_rec(
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
                Node::Atom(name) => self.atom(name.as_str(), output_ctx),
                Node::App(op, children) => {
                    let children = children
                        .into_iter()
                        .map(|child| {
                            let child = child.weaken(&by);
                            self.remap_variables_rec(&child, output_ctx, &replacements, memo)
                        })
                        .collect();
                    self.app(op.as_str(), children)
                }
                Node::Lam(body) => {
                    let body = body.weaken(&by.append(true));
                    let mut under: SmallVec<[Id; 8]> = replacements
                        .iter()
                        .map(|replacement| replacement.in_context(output_ctx + 1).unwrap())
                        .collect();
                    under.push(self.var(output_ctx + 1, output_ctx));
                    let body = self.remap_variables_rec(&body, output_ctx + 1, &under, memo);
                    self.lam(body)
                }
            };
            self.union(&result, &translated);
        }
        self.find_mut(&result)
    }
    pub fn extract(&mut self, target: &Id) -> Option<Term> {
        self.extract_with(target, Term::size)
    }
    /// Extract with a constructor-monotone cost function. The top-down cycle
    /// breaker is sound for costs such as tree size, where wrapping a term
    /// cannot make it cheaper.
    pub fn extract_with(&mut self, target: &Id, cost: impl Fn(&Term) -> usize) -> Option<Term> {
        self.rebuild();
        self.extract_rec(
            target,
            &mut HashMap::default(),
            &mut HashSet::default(),
            &cost,
        )
    }
    fn extract_rec(
        &self,
        target: &Id,
        memo: &mut HashMap<Id, Option<Term>>,
        active_raw: &mut HashSet<RawId>,
        cost: &impl Fn(&Term) -> usize,
    ) -> Option<Term> {
        let target = self.find(target);
        if let Some(result) = memo.get(&target) {
            return result.clone();
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
        memo.insert(target, None);
        let mut best: Option<(usize, Term)> = None;
        for (node, by) in self.nodes_in_class(&target, MatchMode::Lifted) {
            let candidate = match node {
                Node::Var => {
                    if by.dom() != 1 {
                        continue;
                    }
                    let Some(index) = (0..by.cod()).find(|&i| by.get(i)) else {
                        continue;
                    };
                    Term::Var(index)
                }
                Node::Atom(name) => Term::Atom(*name),
                Node::App(op, children) => {
                    let mut terms = Vec::with_capacity(children.len());
                    let mut cyclic = false;
                    for child in children {
                        let child = child.weaken(&by);
                        let Some(term) = self.extract_rec(&child, memo, active_raw, cost) else {
                            cyclic = true;
                            break;
                        };
                        terms.push(term);
                    }
                    if cyclic {
                        continue;
                    }
                    Term::App(*op, terms)
                }
                Node::Lam(body) => {
                    let body = body.weaken(&by.append(true));
                    let Some(body) = self.extract_rec(&body, memo, active_raw, cost) else {
                        continue;
                    };
                    Term::Lam(Box::new(body))
                }
            };
            let candidate_cost = cost(&candidate);
            if best
                .as_ref()
                .is_none_or(|(best_cost, _)| candidate_cost < *best_cost)
            {
                best = Some((candidate_cost, candidate));
            }
        }
        let result = best.map(|(_, term)| term);
        active_raw.remove(&target.raw());
        memo.insert(target, result.clone());
        result
    }
    fn reindex(&mut self) {
        self.rev.clear();
        for (node, &raw) in &self.memo {
            let origin = Id::new(Lift::identity(self.scope[raw as usize]), raw);
            let edge = self.find(&origin);
            self.rev
                .entry(edge.raw())
                .or_default()
                .push((node.clone(), edge.lift()));
        }
        self.rev.sort_keys();
        self.rev_tracked = true;
        self.rev_valid = true;
    }
    /// Convert the temporarily named Miller arguments, in their written
    /// order, to absolute coordinates in the e-graph's ordered context.
    fn miller_arguments(
        top_ctx: usize,
        current_ctx: usize,
        bound: &[usize],
    ) -> Option<SmallVec<[usize; 4]>> {
        let depth = current_ctx.checked_sub(top_ctx)?;
        if bound.iter().any(|&index| index >= depth) {
            return None;
        }
        if bound
            .iter()
            .enumerate()
            .any(|(i, index)| bound[..i].contains(index))
        {
            return None;
        }
        Some(bound.iter().map(|&index| current_ctx - 1 - index).collect())
    }
    /// Abstract pattern-local coordinates into a matcher-level closure. The
    /// body keeps e-graph coordinates ordered; `kept` remembers which
    /// temporary Miller parameter occupied each retained coordinate.
    fn miller_abstract(&self, target: &Id, top_ctx: usize, bound: &[usize]) -> Option<MLam> {
        let mut body = self.find(target);
        let arguments = Self::miller_arguments(top_ctx, body.ctx(), bound)?;
        if (top_ctx..body.ctx())
            .any(|coordinate| body.lift().get(coordinate) && !arguments.contains(&coordinate))
        {
            return None;
        }
        let mut kept: SmallVec<[(usize, usize); 4]> = arguments
            .iter()
            .enumerate()
            .filter_map(|(formal, &coordinate)| {
                body.lift().get(coordinate).then_some((coordinate, formal))
            })
            .collect();
        kept.sort_unstable_by_key(|&(coordinate, _)| coordinate);
        let kept: SmallVec<[usize; 4]> = kept.into_iter().map(|(_, formal)| formal).collect();

        // Delete unused pattern-local coordinates from right to left. Used
        // coordinates remain ordered exactly as the e-graph requires.
        for coordinate in (top_ctx..body.ctx()).rev() {
            if !body.lift().get(coordinate) {
                body = body.remove_coord(coordinate).unwrap();
            }
        }
        debug_assert_eq!(body.ctx(), top_ctx + kept.len());
        Some(MLam::new(top_ctx, bound.len(), &kept, body))
    }
    fn miller_application_coordinates(
        binding: &MLam,
        top_ctx: usize,
        current_ctx: usize,
        bound: &[usize],
    ) -> Option<SmallVec<[usize; 8]>> {
        if binding.top_ctx() != top_ctx || binding.arity() != bound.len() {
            return None;
        }
        let arguments = Self::miller_arguments(top_ctx, current_ctx, bound)?;
        Some(
            (0..top_ctx)
                .chain(binding.kept_indices().map(|formal| arguments[formal]))
                .collect(),
        )
    }
    /// Matching is observational: a repeated metavariable is checked only
    /// when its application remains an ordered lift. Twisted nonlinear
    /// occurrences would require constructing a permuted term, so they fail.
    fn miller_apply_ordered(
        binding: &MLam,
        top_ctx: usize,
        current_ctx: usize,
        bound: &[usize],
    ) -> Option<Id> {
        if bound.is_empty() {
            return (binding.arity() == 0 && binding.top_ctx() == top_ctx)
                .then(|| binding.body.in_context(current_ctx))?;
        }
        let coordinates =
            Self::miller_application_coordinates(binding, top_ctx, current_ctx, bound)?;
        coordinates
            .windows(2)
            .all(|pair| pair[0] < pair[1])
            .then(|| {
                binding
                    .body
                    .weaken(&Lift::selected(current_ctx, &coordinates))
            })
    }
    /// RHS application may construct a term. Ordered applications are still
    /// a single lift; only actual permutations traverse the e-class.
    fn miller_apply(
        &mut self,
        binding: &MLam,
        top_ctx: usize,
        current_ctx: usize,
        bound: &[usize],
    ) -> Option<Id> {
        if bound.is_empty() {
            return (binding.arity() == 0 && binding.top_ctx() == top_ctx)
                .then(|| binding.body.in_context(current_ctx))?;
        }
        let coordinates =
            Self::miller_application_coordinates(binding, top_ctx, current_ctx, bound)?;
        Some(self.remap_variables(&binding.body, current_ctx, &coordinates))
    }
    fn ematch_rec(
        &self,
        pattern: &Pattern,
        target: &Id,
        subst: Subst,
        mode: MatchMode,
        top_ctx: usize,
    ) -> Vec<Subst> {
        match pattern {
            Pattern::Var(name, bound) => match subst.get(name).cloned() {
                Some(previous)
                    if Self::miller_apply_ordered(&previous, top_ctx, target.ctx(), bound)
                        .is_some_and(|applied| self.equivalent(&applied, target)) =>
                {
                    vec![subst]
                }
                Some(_) => vec![],
                None => {
                    let Some(binding) = self.miller_abstract(target, top_ctx, bound) else {
                        return vec![];
                    };
                    let mut next = subst;
                    next.insert(*name, binding);
                    vec![next]
                }
            },
            Pattern::Coord(index) => self
                .nodes_in_class(target, mode)
                .into_iter()
                .filter(|(node, by)| {
                    matches!(node, Node::Var)
                        && *index < top_ctx
                        && *by == Lift::select(target.ctx(), *index)
                })
                .map(|_| subst.clone())
                .collect(),
            Pattern::Bound(index) => self
                .nodes_in_class(target, mode)
                .into_iter()
                .filter(|(node, by)| {
                    let depth = target.ctx() - top_ctx;
                    matches!(node, Node::Var)
                        && *index < depth
                        && *by == Lift::select(target.ctx(), target.ctx() - 1 - *index)
                })
                .map(|_| subst.clone())
                .collect(),
            Pattern::Atom(name) => self
                .nodes_in_class(target, mode)
                .into_iter()
                .filter(|(node, _)| matches!(node, Node::Atom(s) if s == name))
                .map(|_| subst.clone())
                .collect(),
            Pattern::App(op, args) => {
                let mut out = vec![];
                let nodes: Vec<_> = self
                    .nodes_in_class(target, mode)
                    .into_iter()
                    .map(|(node, by)| (node.clone(), by))
                    .collect();
                for (node, by) in nodes {
                    let Node::App(head, children) = node else {
                        continue;
                    };
                    if &head != op || children.len() != args.len() {
                        continue;
                    }
                    let mut partial = vec![subst.clone()];
                    for (arg, child) in args.iter().zip(children) {
                        let lifted = child.weaken(&by);
                        partial = partial
                            .into_iter()
                            .flat_map(|s| self.ematch_rec(arg, &lifted, s, mode, top_ctx))
                            .collect();
                    }
                    out.extend(partial);
                }
                out
            }
            Pattern::Lam(body_pattern) => {
                let mut out = vec![];
                let nodes: Vec<_> = self
                    .nodes_in_class(target, mode)
                    .into_iter()
                    .map(|(node, by)| (node.clone(), by))
                    .collect();
                for (node, by) in nodes {
                    let Node::Lam(body) = node else { continue };
                    let lifted = body.weaken(&by.append(true));
                    out.extend(self.ematch_rec(
                        body_pattern,
                        &lifted,
                        subst.clone(),
                        mode,
                        top_ctx,
                    ));
                }
                out
            }
            // `#subst` computes a term during RHS instantiation; it is not an
            // e-node and therefore cannot match anything on a left-hand side.
            Pattern::Subst(_, _) => vec![],
        }
    }
    pub fn ematch(&self, pattern: &Pattern, target: &Id) -> Vec<Subst> {
        self.ematch_rec(
            pattern,
            target,
            Subst::default(),
            MatchMode::Canonical,
            target.ctx(),
        )
    }
    pub fn ematch_lifted(&self, pattern: &Pattern, target: &Id) -> Vec<Subst> {
        self.ematch_rec(
            pattern,
            target,
            Subst::default(),
            MatchMode::Lifted,
            target.ctx(),
        )
    }
    /// Match a pattern against every canonical e-class placement.
    pub fn search(&mut self, pattern: &Pattern) -> Vec<(usize, Subst)> {
        self.rebuild();
        let targets = self.canonical_targets();
        let mut matches = vec![];
        for target in targets {
            let context = target.ctx();
            matches.extend(
                self.ematch(pattern, &target)
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
            Pattern::Var(name, bound) => {
                let binding = subst.get(name)?.clone();
                self.miller_apply(&binding, top_ctx, ctx, bound)
            }
            Pattern::Coord(index) => (*index < top_ctx).then(|| self.var(ctx, *index)),
            Pattern::Bound(index) => {
                let depth = ctx.checked_sub(top_ctx)?;
                (*index < depth).then(|| self.var(ctx, ctx - 1 - *index))
            }
            Pattern::Atom(name) => Some(self.atom(name.as_str(), ctx)),
            Pattern::App(op, children) => {
                let children: Option<Vec<_>> = children
                    .iter()
                    .map(|p| self.try_instantiate_rec(p, ctx, top_ctx, subst))
                    .collect();
                Some(self.app(op.as_str(), children?))
            }
            Pattern::Lam(body) => {
                let body = self.try_instantiate_rec(body, ctx + 1, top_ctx, subst)?;
                Some(self.lam(body))
            }
            Pattern::Subst(body, replacement) => {
                let body = self.try_instantiate_rec(body, ctx + 1, top_ctx, subst)?;
                let replacement = self.try_instantiate_rec(replacement, ctx, top_ctx, subst)?;
                Some(self.substitute(&body, ctx, &replacement))
            }
        }
    }
    /// Search every stored node in its own context, then apply a rewrite.
    pub fn rewrite_once(&mut self, lhs: &Pattern, rhs: &Pattern) -> usize {
        self.rebuild();
        let mut matches = vec![];
        let raws: Vec<_> = self.memo.values().copied().collect();
        for raw in raws {
            let target = Id::new(Lift::identity(self.scope[raw as usize]), raw);
            for subst in self.ematch(lhs, &target) {
                matches.push((target, subst));
            }
        }
        self.rev_tracked = rhs.may_permute(0);
        let mut applied = 0;
        for (target, subst) in matches {
            let Some(replacement) = self.try_instantiate(rhs, target.ctx(), &subst) else {
                continue;
            };
            if self.union(&target, &replacement) {
                applied += 1;
            }
        }
        if applied > 0 || !self.rev_valid {
            self.rebuild();
        }
        applied
    }
    fn canonical_targets(&self) -> Vec<Id> {
        let mut targets = HashSet::default();
        for &raw in self.memo.values() {
            targets.insert(self.find(&Id::new(Lift::identity(self.scope[raw as usize]), raw)));
        }
        let mut targets: Vec<_> = targets.into_iter().collect();
        targets.sort_by_key(|id| (id.raw(), id.lift().cod(), id.lift().selected_bits()));
        targets
    }
    pub fn saturate(&mut self, rules: &[(Pattern, Pattern)]) -> usize {
        self.saturate_limit(rules, usize::MAX)
    }
    pub fn saturate_limit(&mut self, rules: &[(Pattern, Pattern)], limit: usize) -> usize {
        self.rebuild();
        let mut rounds = 0;
        while rounds < limit {
            let targets = self.canonical_targets();
            let mut matches = vec![];
            for (rule, (lhs, _)) in rules.iter().enumerate() {
                for target in &targets {
                    for subst in self.ematch(lhs, target) {
                        matches.push((rule, *target, subst));
                    }
                }
            }
            self.rev_tracked = rules.iter().any(|(_, rhs)| rhs.may_permute(0));
            let mut changed = false;
            for (rule, target, subst) in matches {
                if let Some(replacement) =
                    self.try_instantiate(&rules[rule].1, target.ctx(), &subst)
                {
                    changed |= self.union(&target, &replacement);
                }
            }
            changed |= self.rebuild();
            if !changed {
                return rounds;
            }
            rounds += 1;
        }
        rounds
    }
    pub fn saturate_beta(&mut self) -> usize {
        self.saturate_beta_limit(usize::MAX)
    }
    pub fn saturate_beta_limit(&mut self, limit: usize) -> usize {
        self.rebuild();
        let lhs = Pattern::app(
            "app",
            vec![
                Pattern::Lam(Box::new(Pattern::Var("?body".into(), vec![0]))),
                Pattern::Var("?arg".into(), vec![]),
            ],
        );
        let rhs = Pattern::Subst(
            Box::new(Pattern::Var("?body".into(), vec![0])),
            Box::new(Pattern::Var("?arg".into(), vec![])),
        );
        let mut rounds = 0;
        while rounds < limit {
            let before_nodes = self.memo.len();
            let targets = self.canonical_targets();

            let mut matches = vec![];
            for target in targets {
                for subst in self.ematch(&lhs, &target) {
                    matches.push((target, subst));
                }
            }
            let mut changed = false;
            for (redex, subst) in matches {
                if let Some(reduced) = self.try_instantiate(&rhs, redex.ctx(), &subst) {
                    changed |= self.union(&redex, &reduced);
                }
            }
            changed |= self.rebuild();
            changed |= before_nodes != self.memo.len();
            if !changed {
                return rounds;
            }
            rounds += 1;
        }
        rounds
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
                Node::App(op, children) => {
                    let children = children.iter().map(Id::show).collect::<Vec<_>>().join(" ");
                    format!("({} {children})", symbol_text(*op))
                }
                Node::Lam(body) => format!("(lam {})", body.show()),
            }
        }

        self.rebuild();
        let classes: Vec<_> = (0..self.parent.len() as RawId)
            .filter(|&raw| self.parent[raw as usize].raw() == raw)
            .map(|raw| {
                (
                    raw,
                    self.scope[raw as usize],
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
            let representative = self.extract(&id).map_or_else(
                || "<recursive>".into(),
                |term| term.display_in(ctx).to_string(),
            );
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
        if self.rev_valid {
            return false;
        }
        let mut any_changed = false;
        loop {
            let nodes = std::mem::take(&mut self.memo);
            let mut changed = false;
            for (node, raw) in nodes {
                let old = Id::new(Lift::identity(self.scope[raw as usize]), raw);
                let (lift, canonical) = self.canonical_node(&node);
                if lift != Lift::identity(self.scope[raw as usize]) || canonical != node {
                    any_changed = true;
                }
                let base = if let Some(&existing) = self.memo.get(&canonical) {
                    self.find_mut(&Id::new(Lift::identity(lift.dom()), existing))
                } else if lift == Lift::identity(self.scope[raw as usize]) {
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
