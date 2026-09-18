//! - a de Bruijn index counts outward from the nearest binder;
//! - a de Bruijn level counts a varialble coming down from an ambient context;
//!
//!
//! During pattern matching, `top_ctx` is the ambient context at the top of the

//! pattern and `current_ctx` additionally includes locally introduced variables from binders at the end
//! pattern variables need to be carried up to the context at the top of the pattern to be carried over to the right hand side

//! The Miller patterns give a description of how you want this carrying to work and which variables you want to allow in the pattern variable

//! A lift embeds an context into another by adding unused variables into the context

use indexmap::IndexMap;
use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
use smallvec::SmallVec;
use symbol_table::GlobalSymbol as Symbol;
use web_time::{Duration, Instant};

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
    App(Symbol, SmallVec<[Id; 2]>),
    Lam(Id),
}

// On 64-bit hosts, Node occupies one 32-byte chunk. This keeps two nodes in a
// typical 64-byte cache line and is why binary children are stored inline.
#[cfg(target_pointer_width = "64")]
const _: () = assert!(std::mem::size_of::<Node>() == 32);

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Pattern {
    /// A metavariable application. Match patterns restrict its arguments to
    /// distinct `BVar`s (Miller form); rewrite templates may use arbitrary
    /// terms, which are simultaneously substituted into the captured body.
    MetaVar(Symbol, Vec<Pattern>),
    /// A free variable from the context outside the pattern, stored as a
    /// de Bruijn level in that ambient context.
    FVar(DeBruijnLevel),
    /// A bound variable introduced inside the pattern, stored as a de Bruijn
    /// index counting outward from the nearest pattern binder.
    BVar(DeBruijnIndex),
    Atom(Symbol),
    App(Symbol, Vec<Pattern>),
    Lam(Box<Pattern>),
    /// Built-in capture-avoiding substitution. Its body is parsed beneath
    /// one additional binder and the result lives outside that binder.
    Subst(Box<Pattern>, Box<Pattern>),
}

impl Pattern {
    pub fn meta(name: &str) -> Self {
        Self::MetaVar(name.into(), vec![])
    }
    pub fn miller(name: &str, arguments: Vec<usize>) -> Self {
        Self::MetaVar(
            name.into(),
            arguments
                .into_iter()
                .map(|index| Self::BVar(index.into()))
                .collect(),
        )
    }
    pub fn atom(name: &str) -> Self {
        Self::Atom(name.into())
    }
    pub fn app(op: &str, children: Vec<Self>) -> Self {
        Self::App(op.into(), children)
    }

    fn miller_indices(arguments: &[Pattern]) -> Option<SmallVec<[DeBruijnIndex; 4]>> {
        arguments
            .iter()
            .map(|argument| match argument {
                Pattern::BVar(index) => Some(*index),
                _ => None,
            })
            .collect()
    }

    /// Whether instantiating this template may need to traverse an e-class.
    /// Ordered bound-variable applications remain a packed lift; permutations
    /// and general term arguments require simultaneous substitution.
    fn needs_binding_traversal(&self, depth: usize) -> bool {
        match self {
            Self::MetaVar(_, arguments) => {
                let Some(indices) = Self::miller_indices(arguments) else {
                    return true;
                };
                occurrence_lift(0, depth, &indices).is_none()
            }
            Self::App(_, children) => children
                .iter()
                .any(|child| child.needs_binding_traversal(depth)),
            Self::Lam(body) => body.needs_binding_traversal(depth + 1),
            Self::Subst(body, replacement) => {
                body.needs_binding_traversal(depth + 1)
                    || replacement.needs_binding_traversal(depth)
            }
            Self::FVar(_) | Self::BVar(_) | Self::Atom(_) => false,
        }
    }

    fn validate_arguments(
        name: Symbol,
        arguments: &[DeBruijnIndex],
        depth: usize,
    ) -> Result<(), String> {
        if arguments.iter().any(|index| index.get() >= depth) {
            return Err(format!(
                "Miller metavariable '{name}' refers outside the pattern binders"
            ));
        }
        if arguments
            .iter()
            .enumerate()
            .any(|(i, index)| arguments[..i].contains(index))
        {
            return Err(format!(
                "Miller metavariable '{name}' repeats a pattern binder"
            ));
        }
        Ok(())
    }

    /// Validate a match pattern and return the arity of every metavariable.
    /// LHS Miller arguments must follow the e-graph's outer-to-inner order.
    fn match_metavariables(&self) -> Result<HashMap<Symbol, usize>, String> {
        fn go(
            pattern: &Pattern,
            depth: usize,
            arities: &mut HashMap<Symbol, usize>,
        ) -> Result<(), String> {
            match pattern {
                Pattern::MetaVar(name, arguments) => {
                    let Some(indices) = Pattern::miller_indices(arguments) else {
                        return Err(format!(
                            "match metavariable '{name}' may only be applied to bound variables"
                        ));
                    };
                    Pattern::validate_arguments(*name, &indices, depth)?;
                    if occurrence_lift(0, depth, &indices).is_none() {
                        let mut correct = indices.to_vec();
                        correct.sort_unstable_by_key(|index| std::cmp::Reverse(index.get()));
                        let correct = correct
                            .iter()
                            .map(|index| format!("#{}", index.get()))
                            .collect::<Vec<_>>()
                            .join(" ");
                        return Err(format!(
                            "Miller metavariable '{name}' arguments are out of order; write ({name} {correct}) on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed"
                        ));
                    }
                    if let Some(previous) = arities.get(name) {
                        if *previous != indices.len() {
                            return Err(format!(
                                "Miller metavariable '{name}' has inconsistent arity in match pattern"
                            ));
                        }
                    } else {
                        arities.insert(*name, indices.len());
                    }
                    Ok(())
                }
                Pattern::App(_, children) => {
                    for child in children {
                        go(child, depth, arities)?;
                    }
                    Ok(())
                }
                Pattern::Lam(body) => go(body, depth + 1, arities),
                Pattern::Subst(_, _) => {
                    Err("#subst is only allowed on a rewrite right-hand side".into())
                }
                Pattern::BVar(index) if index.get() >= depth => {
                    Err("bound variable refers outside the pattern binders".into())
                }
                Pattern::FVar(_) | Pattern::BVar(_) | Pattern::Atom(_) => Ok(()),
            }
        }

        let mut arities = HashMap::default();
        go(self, 0, &mut arities)?;
        Ok(arities)
    }

    /// Reject malformed or out-of-order Miller applications and constructs
    /// such as `#subst` that cannot be observed during matching.
    pub fn validate_match_pattern(&self) -> Result<(), String> {
        self.match_metavariables().map(|_| ())
    }

    fn validate_template(&self, metavariables: &HashMap<Symbol, usize>) -> Result<(), String> {
        fn go(
            pattern: &Pattern,
            depth: usize,
            metavariables: &HashMap<Symbol, usize>,
        ) -> Result<(), String> {
            match pattern {
                Pattern::MetaVar(name, arguments) => {
                    let Some(&arity) = metavariables.get(name) else {
                        return Err(format!(
                            "rewrite right-hand side uses unbound metavariable '{name}'"
                        ));
                    };
                    if arguments.len() != arity {
                        return Err(format!(
                            "Miller metavariable '{name}' has arity {} on the left and {} on the right",
                            arity,
                            arguments.len()
                        ));
                    }
                    for argument in arguments {
                        go(argument, depth, metavariables)?;
                    }
                    Ok(())
                }
                Pattern::App(_, children) => {
                    for child in children {
                        go(child, depth, metavariables)?;
                    }
                    Ok(())
                }
                Pattern::Lam(body) => go(body, depth + 1, metavariables),
                Pattern::Subst(body, replacement) => {
                    go(body, depth + 1, metavariables)?;
                    go(replacement, depth, metavariables)
                }
                Pattern::BVar(index) if index.get() >= depth => {
                    Err("bound variable refers outside the pattern binders".into())
                }
                Pattern::FVar(_) | Pattern::BVar(_) | Pattern::Atom(_) => Ok(()),
            }
        }

        go(self, 0, metavariables)
    }
}

/// A statically checked rewrite. Validation guarantees that the left-hand
/// side is observable and every right-hand metavariable has a compatible
/// binding. The traversal flag is cached for the application phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rewrite {
    lhs: Pattern,
    rhs: Pattern,
    rhs_needs_traversal: bool,
}

impl Rewrite {
    pub fn new(lhs: Pattern, rhs: Pattern) -> Result<Self, String> {
        let metavariables = lhs.match_metavariables()?;
        rhs.validate_template(&metavariables)?;
        let rhs_needs_traversal = rhs.needs_binding_traversal(0);
        Ok(Self {
            lhs,
            rhs,
            rhs_needs_traversal,
        })
    }
    pub fn lhs(&self) -> &Pattern {
        &self.lhs
    }
    pub fn rhs(&self) -> &Pattern {
        &self.rhs
    }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    FVar(DeBruijnLevel),
    BVar(DeBruijnIndex),
    Atom(Symbol),
    App(Symbol, Vec<Term>),
    Lam(Box<Term>),
}

impl Term {
    pub fn size(&self) -> usize {
        match self {
            Self::FVar(_) | Self::BVar(_) | Self::Atom(_) => 1,
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
            Self::FVar(level) => write!(f, "${}", level.get()),
            Self::BVar(index) => write!(f, "#{}", index.get()),
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

/// An extracted term together with the size of its free-variable context.
/// `FVar` levels refer to this scope; `BVar` indices refer to enclosing `Lam`s.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermCtx {
    pub scope: usize,
    pub t: Term,
}

impl TermCtx {
    pub fn size(&self) -> usize {
        self.t.size()
    }

    /// Render with generated names for binders and `$n` for free variables.
    pub fn display(&self) -> NamedTerm<'_> {
        self.display_with_root_binders(&[])
    }

    /// Name the final free variables as Miller formal parameters. Variables
    /// before them remain `$n` references to the outer context.
    pub fn display_with_root_binders<'a>(&'a self, root_binders: &'a [String]) -> NamedTerm<'a> {
        assert!(root_binders.len() <= self.scope);
        NamedTerm {
            term: self,
            root_binders,
        }
    }
}

impl std::fmt::Display for TermCtx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.t.fmt(f)
    }
}

pub struct NamedTerm<'a> {
    term: &'a TermCtx,
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
                Term::FVar(level) if level.get() < outer_ctx => {
                    write!(f, "${}", level.get())
                }
                Term::FVar(level) if level.get() < root_ctx => {
                    f.write_str(&root_binders[level.get() - outer_ctx])
                }
                Term::FVar(level) => write!(f, "${}", level.get()),
                Term::BVar(index) => match binders
                    .len()
                    .checked_sub(index.get() + 1)
                    .and_then(|slot| binders.get(slot))
                {
                    Some(name) => f.write_str(name),
                    None => write!(f, "#{}", index.get()),
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
        let outer_ctx = self.term.scope - self.root_binders.len();
        go(&self.term.t, f, outer_ctx, self.root_binders, &mut vec![])
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

#[derive(Default)]
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
        // Path compression stores an edge in the raw class's intrinsic
        // context. `id` itself may be placed in a larger ambient context.
        debug_assert_eq!(root.ctx(), edge.ctx());
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
        self.atom_symbol(name.into(), ctx)
    }
    fn atom_symbol(&mut self, name: Symbol, ctx: usize) -> Id {
        let base = self.intern(0, Node::Atom(name));
        base.weaken(&Lift::unused(ctx))
    }
    pub fn app(&mut self, op: &str, children: Vec<Id>) -> Id {
        self.app_symbol(op.into(), children.into())
    }
    fn app_symbol(&mut self, op: Symbol, children: SmallVec<[Id; 2]>) -> Id {
        assert!(!children.is_empty());
        let ctx = children[0].ctx();
        assert!(children.iter().all(|c| c.ctx() == ctx));
        let (common, node) = self.canonical_node(&Node::App(op, children));
        let base = self.intern(common.dom(), node);
        base.weaken(&common)
    }
    /// The bound variable is the final variable in the body's context.
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
                let children: SmallVec<[_; 2]> =
                    children.iter().map(|c| self.find_mut(c)).collect();
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
                let origin = Id::new(Lift::identity(self.parent[raw as usize].ctx()), raw);
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
                Node::App(op, children) => {
                    let children = children
                        .into_iter()
                        .map(|child| {
                            let child = child.weaken(&by);
                            self.substitute_many_rec(&child, output_ctx, &replacements, memo)
                        })
                        .collect();
                    self.app_symbol(op, children)
                }
                Node::Lam(body) => {
                    let body = body.weaken(&by.append(true));
                    let mut under: SmallVec<[Id; 8]> = replacements
                        .iter()
                        .map(|replacement| replacement.in_context(output_ctx + 1).unwrap())
                        .collect();
                    under.push(self.var(output_ctx + 1, output_ctx));
                    let body = self.substitute_many_rec(&body, output_ctx + 1, &under, memo);
                    self.lam(body)
                }
            };
            self.union(&result, &translated);
        }
        self.find_mut(&result)
    }
    pub fn extract(&mut self, target: &Id) -> Option<TermCtx> {
        self.extract_with(target, Term::size)
    }
    /// Extract with a constructor-monotone cost function. The top-down cycle
    /// breaker is sound for costs such as tree size, where wrapping a term
    /// cannot make it cheaper.
    pub fn extract_with(&mut self, target: &Id, cost: impl Fn(&Term) -> usize) -> Option<TermCtx> {
        self.rebuild();
        let target = self.find(target);
        let scope = target.ctx();
        let t = self.extract_rec(
            &target,
            scope,
            &mut HashMap::default(),
            &mut HashSet::default(),
            &cost,
        )?;
        Some(TermCtx { scope, t })
    }
    fn extract_rec(
        &self,
        target: &Id,
        root_scope: usize,
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
                    if index < root_scope {
                        Term::FVar(index.into())
                    } else {
                        let binder = target.ctx().checked_sub(index + 1)?;
                        Term::BVar(binder.into())
                    }
                }
                Node::Atom(name) => Term::Atom(*name),
                Node::App(op, children) => {
                    let mut terms = Vec::with_capacity(children.len());
                    let mut cyclic = false;
                    for child in children {
                        let child = child.weaken(&by);
                        let Some(term) =
                            self.extract_rec(&child, root_scope, memo, active_raw, cost)
                        else {
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
                    let Some(body) = self.extract_rec(&body, root_scope, memo, active_raw, cost)
                    else {
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
            let origin = Id::new(Lift::identity(self.parent[raw as usize].ctx()), raw);
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
            Pattern::App(op, args) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    let Node::App(head, children) = node else {
                        continue;
                    };
                    if head != op || children.len() != args.len() {
                        continue;
                    }
                    let mut partial: MatchResults = smallvec::smallvec![subst.clone()];
                    for (arg, child) in args.iter().zip(children) {
                        let lifted = child.weaken(&by);
                        let mut next = MatchResults::new();
                        for partial_subst in partial {
                            self.ematch_rec(arg, &lifted, partial_subst, mode, top_ctx, &mut next);
                        }
                        partial = next;
                        if partial.is_empty() {
                            break;
                        }
                    }
                    out.extend(partial);
                }
            }
            Pattern::Lam(body_pattern) => {
                for (node, by) in self.nodes_in_class(target, mode) {
                    let Node::Lam(body) = node else { continue };
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
            Pattern::App(op, children) => {
                let children: Option<SmallVec<[Id; 2]>> = children
                    .iter()
                    .map(|p| self.try_instantiate_rec(p, ctx, top_ctx, subst))
                    .collect();
                Some(self.app_symbol(*op, children?))
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
    fn canonical_targets(&self) -> Vec<Id> {
        let mut targets = HashSet::default();
        for &raw in self.memo.values() {
            targets.insert(self.find(&Id::new(
                Lift::identity(self.parent[raw as usize].ctx()),
                raw,
            )));
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
        let mut matches_by_rule: Vec<Vec<(Id, Subst)>> =
            (0..rules.len()).map(|_| Vec::new()).collect();
        while stats.rounds < limit {
            let before_nodes = self.memo.len();

            let start = Instant::now();
            let targets = self.canonical_targets();
            for (rule, matches) in rules.iter().zip(&mut matches_by_rule) {
                matches.clear();
                for target in &targets {
                    for subst in self.ematch_with(&rule.lhs, target, MatchMode::Canonical) {
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
                    if let Some(replacement) = self.try_instantiate(&rule.rhs, target.ctx(), &subst)
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
