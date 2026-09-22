use super::{DeBruijnIndex, DeBruijnLevel, occurrence_lift};
use rustc_hash::FxHashMap as HashMap;
use smallvec::SmallVec;
use symbol_table::GlobalSymbol as Symbol;

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
    /// Binary, curried application.
    App(Box<Pattern>, Box<Pattern>),
    Binder(Symbol, Box<Pattern>),
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
    pub fn apps(op: &str, arguments: Vec<Self>) -> Self {
        assert!(!arguments.is_empty());
        arguments.into_iter().fold(Self::atom(op), Self::app)
    }
    pub fn app(function: Self, argument: Self) -> Self {
        Self::App(Box::new(function), Box::new(argument))
    }
    pub fn binder(op: &str, body: Self) -> Self {
        Self::Binder(op.into(), Box::new(body))
    }

    pub(crate) fn miller_indices(arguments: &[Pattern]) -> Option<SmallVec<[DeBruijnIndex; 4]>> {
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
            Self::App(function, argument) => {
                function.needs_binding_traversal(depth) || argument.needs_binding_traversal(depth)
            }
            Self::Binder(_, body) => body.needs_binding_traversal(depth + 1),
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
    pub(crate) fn match_metavariables(&self) -> Result<HashMap<Symbol, usize>, String> {
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
                            "Miller metavariable '{name}' arguments are out of order; write {{{name} {correct}}} on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed"
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
                Pattern::App(function, argument) => {
                    go(function, depth, arities)?;
                    go(argument, depth, arities)
                }
                Pattern::Binder(_, body) => go(body, depth + 1, arities),
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
                Pattern::App(function, argument) => {
                    go(function, depth, metavariables)?;
                    go(argument, depth, metavariables)
                }
                Pattern::Binder(_, body) => go(body, depth + 1, metavariables),
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
    pub(crate) rhs_needs_traversal: bool,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    FVar(DeBruijnLevel),
    BVar(DeBruijnIndex),
    Atom(Symbol),
    /// Binary, curried application.
    App(Box<Term>, Box<Term>),
    Binder(Symbol, Box<Term>),
}

impl Term {
    pub fn size(&self) -> usize {
        match self {
            Self::FVar(_) | Self::BVar(_) | Self::Atom(_) => 1,
            Self::App(function, argument) => 1 + function.size() + argument.size(),
            Self::Binder(_, body) => 1 + body.size(),
        }
    }
}

/// Whether an atom must be printed quoted. The delimiter set mirrors the
/// frontend lexer's, so that printed output re-reads as the same atom.
fn needs_quoting(text: &str) -> bool {
    text.is_empty()
        || text.starts_with(['?', '$'])
        || text.chars().any(|c| {
            c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ';' | '"')
        })
}

/// Write an atom, quoting and escaping it when it cannot be written bare.
/// `force_quote` additionally quotes a name that would otherwise capture a
/// binder in scope.
fn write_atom(f: &mut std::fmt::Formatter<'_>, text: &str, force_quote: bool) -> std::fmt::Result {
    if !force_quote && !needs_quoting(text) {
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

impl std::fmt::Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn atom(f: &mut std::fmt::Formatter<'_>, text: &str) -> std::fmt::Result {
            write_atom(f, text, false)
        }
        fn bin_head(term: &Term, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            if let Term::App(function, argument) = term {
                bin_head(function, f)?;
                write!(f, " {argument}")
            } else {
                write!(f, "{term}")
            }
        }
        match self {
            Self::FVar(level) => write!(f, "${}", level.get()),
            Self::BVar(index) => write!(f, "#{}", index.get()),
            Self::Atom(name) => atom(f, name.as_str()),
            Self::App(function, argument) => {
                f.write_str("(")?;
                bin_head(function, f)?;
                write!(f, " {argument})")
            }
            Self::Binder(op, body) => write!(f, "(@{op} {body})"),
        }
    }
}

/// An extracted term together with the size of its free-variable context.
/// `FVar` levels refer to this scope; `BVar` indices refer to enclosing binders.
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
        use write_atom as atom;
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
                Term::App(function, argument) => {
                    fn head(
                        term: &Term,
                        f: &mut std::fmt::Formatter<'_>,
                        outer_ctx: usize,
                        root_binders: &[String],
                        binders: &mut Vec<String>,
                    ) -> std::fmt::Result {
                        if let Term::App(function, argument) = term {
                            head(function, f, outer_ctx, root_binders, binders)?;
                            f.write_str(" ")?;
                            go(argument, f, outer_ctx, root_binders, binders)
                        } else {
                            go(term, f, outer_ctx, root_binders, binders)
                        }
                    }
                    f.write_str("(")?;
                    head(function, f, outer_ctx, root_binders, binders)?;
                    f.write_str(" ")?;
                    go(argument, f, outer_ctx, root_binders, binders)?;
                    f.write_str(")")
                }
                Term::Binder(op, body) => {
                    let name = format!("x{}", root_binders.len() + binders.len());
                    write!(f, "(@{op} {name} ")?;
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
