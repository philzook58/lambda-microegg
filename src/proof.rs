use crate::{Id, Lift, Pattern, RawId, Rewrite, Subst};
use rustc_hash::FxHashMap as HashMap;

/// The original syntax allocated at a raw e-class ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EGraphTermDefinition {
    Atom(String),
    Var,
    App(Id, Id),
    Restrict { source: RawId, thinning: Lift },
}

/// Index of one equality reason retained by the explanation forest.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct ReasonId(u32);

/// One instantiated pattern node and its current representative.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PatternNodeWitness {
    pub(crate) raw: Id,
    pub(crate) normal: Id,
}

/// Index of a named rewrite rule shared by all its successful applications.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct RuleId(u32);

/// Extra normalization data needed when the union endpoints are not literally the rule instance.
#[derive(Clone, Debug)]
pub(crate) struct RewriteNormalization {
    /// One `(instantiated node, representative)` pair per left pattern node, in postorder.
    pub(crate) left: Vec<PatternNodeWitness>,
    /// One `(instantiated node, representative)` pair per right pattern node, in postorder.
    pub(crate) right: Vec<PatternNodeWitness>,
}

/// An equality reason together with the two contextual terms it connects.
#[derive(Clone, Debug)]
struct ReasonNode {
    left: Id,
    right: Id,
    reason: Reason,
}

/// One parent link in the uncompressed explanation forest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExplainEdge {
    reason: ReasonId,
    thinning: Lift,
    reversed: bool,
}

/// Why the endpoints of one explanation-forest edge are equal.
#[derive(Clone, Debug)]
pub(crate) enum Reason {
    /// The two raw IDs unfold to the same atom or application.
    Definitional,
    /// An equality supplied directly by the caller.
    Assumption {
        index: usize,
        label: String,
    },
    /// One successful application of a named rewrite rule.
    Rewrite {
        rule: RuleId,
        subst: Subst,
        normalization: Option<RewriteNormalization>,
    },
    /// Two applications whose function and argument classes were already equal.
    Congruence {
        left_function: Id,
        right_function: Id,
        left_argument: Id,
        right_argument: Id,
    },
    /// Convert the supplied equality into an equality between its current roots.
    RootEquality {
        direct: ReasonId,
        input_left: Id,
        input_right: Id,
        left_root: Id,
        right_root: Id,
    },
    SpecializeLeft {
        equality: ReasonId,
        left: Lift,
    },
    SpecializeRight {
        equality: ReasonId,
        right: Lift,
    },
    FactorLeft {
        equality: ReasonId,
        left: Lift,
        common: Lift,
    },
    FactorRight {
        equality: ReasonId,
        right: Lift,
    },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EGraphProofTrace {
    // Source terms, indexed by RawId.
    definitions: Vec<Option<EGraphTermDefinition>>,
    contexts: Vec<usize>,
    // A second, uncompressed union-find forest used only for explanations.
    explain_parents: Vec<RawId>,
    explain_edges: Vec<Option<ExplainEdge>>,
    explain_sizes: Vec<usize>,
    // Each forest edge points into this table.
    reasons: Vec<ReasonNode>,
    // Named rules are shared by all their successful applications.
    rules: Vec<Rewrite>,
    assumptions: usize,
    unsupported: Option<String>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EGraphProofStats {
    pub explanation_edges: usize,
    pub explanation_reasons: usize,
}

impl EGraphProofTrace {
    pub(crate) fn register_rule(&mut self, rule: &Rewrite) -> Option<RuleId> {
        fn supported(pattern: &Pattern) -> bool {
            match pattern {
                Pattern::MetaVar(_, arguments) => arguments.is_empty(),
                Pattern::Atom(_) => true,
                Pattern::App(function, argument) => supported(function) && supported(argument),
                _ => false,
            }
        }
        if rule.name().is_none() || !supported(rule.lhs()) || !supported(rule.rhs()) {
            return None;
        }
        let id = RuleId(self.rules.len() as u32);
        self.rules.push(rule.clone());
        Some(id)
    }

    pub(crate) fn make_set(&mut self, raw: RawId, context: usize) {
        assert_eq!(self.definitions.len(), raw as usize);
        self.definitions.push(None);
        self.contexts.push(context);
        self.explain_parents.push(raw);
        self.explain_edges.push(None);
        self.explain_sizes.push(1);
    }

    pub(crate) fn define_restriction(&mut self, raw: RawId, source: RawId, thinning: Lift) {
        debug_assert_eq!(self.contexts[raw as usize], thinning.dom());
        self.define(raw, EGraphTermDefinition::Restrict { source, thinning });
    }

    pub(crate) fn define(&mut self, raw: RawId, definition: EGraphTermDefinition) {
        let slot = &mut self.definitions[raw as usize];
        if slot.is_none() {
            *slot = Some(definition);
        }
    }

    pub(crate) fn unsupported(&mut self, message: impl Into<String>) {
        if self.unsupported.is_none() {
            self.unsupported = Some(message.into());
        }
    }

    pub(crate) fn definition(&self, raw: RawId) -> Option<EGraphTermDefinition> {
        self.definitions[raw as usize].clone()
    }

    pub(crate) fn assumption(&mut self, label: String) -> Reason {
        let index = self.assumptions;
        self.assumptions += 1;
        Reason::Assumption { index, label }
    }

    fn explanation_root(&self, mut raw: RawId) -> RawId {
        loop {
            let parent = self.explain_parents[raw as usize];
            if parent == raw {
                return raw;
            }
            raw = parent;
        }
    }

    fn reroot_explanation(&mut self, raw: RawId) {
        let old_root = self.explanation_root(raw);
        let size = self.explain_sizes[old_root as usize];
        let mut current = raw;
        let mut parent = self.explain_parents[current as usize];
        let mut edge = self.explain_edges[current as usize].take();
        self.explain_parents[current as usize] = current;

        while parent != current {
            let next_parent = self.explain_parents[parent as usize];
            let next_edge = self.explain_edges[parent as usize].take();
            let current_edge = edge.expect("a non-root explanation node has an edge");
            self.explain_parents[parent as usize] = current;
            self.explain_edges[parent as usize] = Some(ExplainEdge {
                reason: current_edge.reason,
                thinning: current_edge.thinning,
                reversed: !current_edge.reversed,
            });
            current = parent;
            parent = next_parent;
            edge = next_edge;
        }

        if old_root != raw {
            self.explain_sizes[old_root as usize] = 0;
            self.explain_sizes[raw as usize] = size;
        }
    }

    fn explanation_paths(&self, left: RawId, right: RawId) -> (Vec<ExplainEdge>, Vec<ExplainEdge>) {
        let mut left_depths = vec![None; self.explain_parents.len()];
        let mut left_edges = Vec::new();
        let mut current = left;
        loop {
            left_depths[current as usize] = Some(left_edges.len());
            let parent = self.explain_parents[current as usize];
            if parent == current {
                break;
            }
            left_edges.push(
                self.explain_edges[current as usize]
                    .expect("a non-root explanation node has an edge"),
            );
            current = parent;
        }

        let mut right_edges = Vec::new();
        current = right;
        let common_depth = loop {
            if let Some(depth) = left_depths[current as usize] {
                break depth;
            }
            let parent = self.explain_parents[current as usize];
            assert_ne!(
                parent, current,
                "equivalent e-classes must share an explanation root"
            );
            right_edges.push(
                self.explain_edges[current as usize]
                    .expect("a non-root explanation node has an edge"),
            );
            current = parent;
        };
        left_edges.truncate(common_depth);
        (left_edges, right_edges)
    }

    fn alloc_reason(&mut self, node: ReasonNode) -> ReasonId {
        assert!(
            self.reasons.len() <= u32::MAX as usize,
            "exhausted reason IDs"
        );
        let reason = ReasonId(self.reasons.len() as u32);
        self.reasons.push(node);
        reason
    }

    pub(crate) fn root_equality(
        &mut self,
        input_left: Id,
        input_right: Id,
        left_root: Id,
        right_root: Id,
        reason: Reason,
    ) -> ReasonId {
        let direct = self.alloc_reason(ReasonNode {
            left: input_left,
            right: input_right,
            reason,
        });
        if input_left == left_root && input_right == right_root {
            return direct;
        }
        self.alloc_reason(ReasonNode {
            left: left_root,
            right: right_root,
            reason: Reason::RootEquality {
                direct,
                input_left,
                input_right,
                left_root,
                right_root,
            },
        })
    }

    fn origin(&self, raw: RawId) -> Id {
        Id::new(Lift::identity(self.contexts[raw as usize]), raw)
    }

    fn link_thinning_reason(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        reason: ReasonId,
    ) {
        let left_root = self.explanation_root(larger);
        let right_root = self.explanation_root(smaller);
        assert_ne!(
            left_root, right_root,
            "a proof edge must join two components"
        );
        if self.explain_sizes[left_root as usize] <= self.explain_sizes[right_root as usize] {
            self.reroot_explanation(larger);
            let right_root = self.explanation_root(smaller);
            let left_size = self.explain_sizes[larger as usize];
            self.explain_parents[larger as usize] = smaller;
            self.explain_edges[larger as usize] = Some(ExplainEdge {
                reason,
                thinning,
                reversed: false,
            });
            self.explain_sizes[larger as usize] = 0;
            self.explain_sizes[right_root as usize] += left_size;
        } else {
            self.reroot_explanation(smaller);
            let left_root = self.explanation_root(larger);
            let right_size = self.explain_sizes[smaller as usize];
            self.explain_parents[smaller as usize] = larger;
            self.explain_edges[smaller as usize] = Some(ExplainEdge {
                reason,
                thinning,
                reversed: true,
            });
            self.explain_sizes[smaller as usize] = 0;
            self.explain_sizes[left_root as usize] += right_size;
        }
    }

    fn link_derived_thinning_equality(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        equality: ReasonId,
        reason: Reason,
    ) {
        let left = self.origin(larger);
        let right = Id::new(thinning, smaller);
        let equality_node = &self.reasons[equality.0 as usize];
        let reason = if equality_node.left == left && equality_node.right == right {
            equality
        } else {
            self.alloc_reason(ReasonNode {
                left,
                right,
                reason,
            })
        };
        self.link_thinning_reason(larger, smaller, thinning, reason);
    }

    pub(crate) fn link_specialize_left(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        equality: ReasonId,
        left: Lift,
    ) {
        self.link_derived_thinning_equality(
            larger,
            smaller,
            thinning,
            equality,
            Reason::SpecializeLeft { equality, left },
        );
    }

    pub(crate) fn link_specialize_right(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        equality: ReasonId,
        right: Lift,
    ) {
        self.link_derived_thinning_equality(
            larger,
            smaller,
            thinning,
            equality,
            Reason::SpecializeRight { equality, right },
        );
    }

    pub(crate) fn link_factor_left(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        equality: ReasonId,
        left: Lift,
        common: Lift,
    ) {
        self.link_derived_thinning_equality(
            larger,
            smaller,
            thinning,
            equality,
            Reason::FactorLeft {
                equality,
                left,
                common,
            },
        );
    }

    pub(crate) fn link_factor_right(
        &mut self,
        larger: RawId,
        smaller: RawId,
        thinning: Lift,
        equality: ReasonId,
        right: Lift,
    ) {
        self.link_derived_thinning_equality(
            larger,
            smaller,
            thinning,
            equality,
            Reason::FactorRight { equality, right },
        );
    }

    pub(crate) fn stats(&self) -> EGraphProofStats {
        EGraphProofStats {
            explanation_edges: self.explain_edges.iter().flatten().count(),
            explanation_reasons: self.reasons.len(),
        }
    }
}

// Lean certificate construction. Everything below is ephemeral for one print request.

/// A partially known lift used only while reconciling two explanation paths.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PartialLift {
    source: Lift,
    target: Lift,
}

impl PartialLift {
    fn new(source: Lift, target: Lift) -> Self {
        assert_eq!(source.dom(), target.dom());
        Self { source, target }
    }

    fn total(lift: Lift) -> Self {
        Self::new(Lift::identity(lift.dom()), lift)
    }

    fn reverse(&self) -> Self {
        Self::new(self.target, self.source)
    }

    fn then(&self, outer: &Self) -> Self {
        assert_eq!(self.target.cod(), outer.source.cod());
        let pullback = self.target.pullback(&outer.source);
        Self::new(
            self.source.compose(&pullback.from_left),
            outer.target.compose(&pullback.from_right),
        )
    }

    fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.source.cod(), other.source.cod());
        assert_eq!(self.target.cod(), other.target.cod());
        let source = self.source.union(&other.source).lift;
        let target = self.target.union(&other.target).lift;
        for partial in [self, other] {
            assert_eq!(
                source.factor(&partial.source),
                target.factor(&partial.target),
                "incompatible partial lifts"
            );
        }
        Self::new(source, target)
    }

    fn finish(&self) -> Lift {
        assert!(self.source.is_identity());
        self.target
    }
}
/// An index into the proof-expression arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofId(pub(crate) u32);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphProofKind {
    Refl,
    Symm(ProofId),
    Trans(ProofId, ProofId),
    Lift {
        proof: ProofId,
        lift: Lift,
    },
    CongApp(ProofId, ProofId),
    CongFunction {
        argument: PlacedTerm,
        proof: ProofId,
    },
    CongArgument {
        function: PlacedTerm,
        proof: ProofId,
    },
    Rewrite {
        name: String,
        arguments: Vec<PlacedTerm>,
    },
    SpecializeLeft {
        equality: ProofId,
        left: Lift,
    },
    SpecializeRight {
        equality: ProofId,
        right: Lift,
    },
    FactorLeft {
        equality: ProofId,
        left: Lift,
        common: Lift,
    },
    FactorRight {
        equality: ProofId,
        right: Lift,
    },
    Assumption {
        index: usize,
        label: String,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct EGraphProofNode {
    left: PlacedTerm,
    right: PlacedTerm,
    kind: EGraphProofKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EGraphTermId(u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct PlacedTerm {
    term: EGraphTermId,
    lift: Lift,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphTermNode {
    Raw(RawId),
    App(PlacedTerm, PlacedTerm),
}

#[derive(Debug, Default)]
struct EGraphProofArena {
    proofs: Vec<EGraphProofNode>,
    proof_memo: HashMap<EGraphProofNode, ProofId>,
    terms: Vec<EGraphTermNode>,
    term_memo: HashMap<EGraphTermNode, EGraphTermId>,
    raw_terms: HashMap<RawId, EGraphTermId>,
    materialized_reasons: Vec<Option<ProofId>>,
}

pub(crate) fn render_egraph_proof(
    trace: &EGraphProofTrace,
    theorem_name: &str,
    binders: &str,
    left: Id,
    right: Id,
) -> Result<String, ProofError> {
    let mut arena = EGraphProofArena::default();
    let conclusion = arena.proof_between(trace, left, right);
    arena.render(trace, theorem_name, binders, left, right, conclusion)
}

impl EGraphProofTrace {
    fn source_term(&self, raw: RawId) -> Result<String, ProofError> {
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphTermDefinition::Atom(name)) => Ok(name.clone()),
            Some(EGraphTermDefinition::Var) => Ok("(fun x0 : α => x0)".to_owned()),
            Some(EGraphTermDefinition::App(function, argument)) => {
                let body = format!(
                    "({}) ({})",
                    self.source_endpoint(*function)?,
                    self.source_endpoint(*argument)?
                );
                Ok(Self::lambda(self.contexts[raw as usize], &body))
            }
            Some(EGraphTermDefinition::Restrict { source, thinning }) => {
                let body = Self::apply(
                    &format!("({})", self.source_term(*source)?),
                    &Self::filled_arguments(*thinning),
                );
                Ok(Self::lambda(thinning.dom(), &body))
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn source_endpoint(&self, id: Id) -> Result<String, ProofError> {
        let source = self.source_term(id.raw())?;
        let arguments = Self::selected_arguments(id.lift());
        Ok(Self::apply(&format!("({source})"), &arguments))
    }

    fn mark_term(&self, raw: RawId, live: &mut [bool]) -> Result<(), ProofError> {
        if std::mem::replace(&mut live[raw as usize], true) {
            return Ok(());
        }
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphTermDefinition::Atom(_) | EGraphTermDefinition::Var) => Ok(()),
            Some(EGraphTermDefinition::App(function, argument)) => {
                self.mark_term(function.raw(), live)?;
                self.mark_term(argument.raw(), live)
            }
            Some(EGraphTermDefinition::Restrict { source, .. }) => self.mark_term(*source, live),
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn variables(arity: usize) -> Vec<String> {
        (0..arity).map(|index| format!("x{index}")).collect()
    }

    fn selected_arguments(lift: Lift) -> Vec<String> {
        (0..lift.cod())
            .filter(|&index| lift.get(index))
            .map(|index| format!("x{index}"))
            .collect()
    }

    fn filled_arguments(lift: Lift) -> Vec<String> {
        let mut selected = 0;
        (0..lift.cod())
            .map(|index| {
                if lift.get(index) {
                    let argument = format!("x{selected}");
                    selected += 1;
                    argument
                } else {
                    "default".to_owned()
                }
            })
            .collect()
    }

    fn subset_arguments(container: Lift, subset: Lift) -> Vec<String> {
        let mut selected = 0;
        (0..container.cod())
            .map(|index| {
                if !container.get(index) {
                    return "default".to_owned();
                }
                let argument = if subset.get(index) {
                    format!("x{selected}")
                } else {
                    "default".to_owned()
                };
                selected += 1;
                argument
            })
            .collect()
    }

    fn apply(function: &str, arguments: &[String]) -> String {
        if arguments.is_empty() {
            function.to_owned()
        } else {
            format!("{function} {}", arguments.join(" "))
        }
    }

    fn lambda(arity: usize, body: &str) -> String {
        if arity == 0 {
            body.to_owned()
        } else {
            format!("(fun {} => {body})", Self::variables(arity).join(" "))
        }
    }
}

impl EGraphProofArena {
    fn alloc(&mut self, left: PlacedTerm, right: PlacedTerm, kind: EGraphProofKind) -> ProofId {
        assert_eq!(left.lift.cod(), right.lift.cod());
        let node = EGraphProofNode { left, right, kind };
        if let Some(&proof) = self.proof_memo.get(&node) {
            return proof;
        }
        assert!(
            self.proofs.len() <= u32::MAX as usize,
            "exhausted proof IDs"
        );
        let proof = ProofId(self.proofs.len() as u32);
        self.proofs.push(node.clone());
        self.proof_memo.insert(node, proof);
        proof
    }

    fn alloc_term(&mut self, node: EGraphTermNode) -> EGraphTermId {
        if let Some(&term) = self.term_memo.get(&node) {
            return term;
        }
        let term = EGraphTermId(self.terms.len() as u32);
        self.terms.push(node.clone());
        self.term_memo.insert(node, term);
        term
    }

    fn raw_term(&mut self, raw: RawId) -> EGraphTermId {
        if let Some(&term) = self.raw_terms.get(&raw) {
            return term;
        }
        let term = self.alloc_term(EGraphTermNode::Raw(raw));
        self.raw_terms.insert(raw, term);
        term
    }

    fn placed(&mut self, id: Id) -> PlacedTerm {
        PlacedTerm {
            term: self.raw_term(id.raw()),
            lift: id.lift(),
        }
    }

    fn app_term(&mut self, function: PlacedTerm, argument: PlacedTerm) -> PlacedTerm {
        assert_eq!(function.lift.cod(), argument.lift.cod());
        let arity = function.lift.cod();
        PlacedTerm {
            term: self.alloc_term(EGraphTermNode::App(function, argument)),
            lift: Lift::identity(arity),
        }
    }

    fn refl_between(&mut self, left: Id, right: Id) -> ProofId {
        let left = self.placed(left);
        let right = self.placed(right);
        self.refl_terms(left, right)
    }

    fn refl_terms(&mut self, left: PlacedTerm, right: PlacedTerm) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Refl)
    }

    fn lift_term(term: PlacedTerm, outer: Lift) -> PlacedTerm {
        PlacedTerm {
            term: term.term,
            lift: outer.compose(&term.lift),
        }
    }

    fn lift_proof(&mut self, proof: ProofId, lift: Lift) -> ProofId {
        if lift.is_identity() {
            return proof;
        }
        let node = &self.proofs[proof.0 as usize];
        self.alloc(
            Self::lift_term(node.left, lift),
            Self::lift_term(node.right, lift),
            EGraphProofKind::Lift { proof, lift },
        )
    }

    fn symm(&mut self, proof: ProofId) -> ProofId {
        let node = &self.proofs[proof.0 as usize];
        if node.left == node.right && matches!(node.kind, EGraphProofKind::Refl) {
            return proof;
        }
        self.alloc(node.right, node.left, EGraphProofKind::Symm(proof))
    }

    fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        let left_node = &self.proofs[left.0 as usize];
        let right_node = &self.proofs[right.0 as usize];
        assert_eq!(
            left_node.right, right_node.left,
            "ill-typed e-graph transitivity"
        );
        if left_node.left == left_node.right && matches!(left_node.kind, EGraphProofKind::Refl) {
            return right;
        }
        if right_node.left == right_node.right && matches!(right_node.kind, EGraphProofKind::Refl) {
            return left;
        }
        self.alloc(
            left_node.left,
            right_node.right,
            EGraphProofKind::Trans(left, right),
        )
    }

    fn congr_app(&mut self, left: Id, right: Id, function: ProofId, argument: ProofId) -> ProofId {
        let left = self.placed(left);
        let right = self.placed(right);
        self.congr_terms_with_endpoints(left, right, function, argument)
    }

    fn congr_terms_with_endpoints(
        &mut self,
        left: PlacedTerm,
        right: PlacedTerm,
        function: ProofId,
        argument: ProofId,
    ) -> ProofId {
        let function_node = &self.proofs[function.0 as usize];
        let argument_node = &self.proofs[argument.0 as usize];
        let function_is_refl = function_node.left == function_node.right
            && matches!(function_node.kind, EGraphProofKind::Refl);
        let argument_is_refl = argument_node.left == argument_node.right
            && matches!(argument_node.kind, EGraphProofKind::Refl);
        if function_is_refl && argument_is_refl {
            return self.refl_terms(left, right);
        }
        if function_is_refl {
            return self.alloc(
                left,
                right,
                EGraphProofKind::CongArgument {
                    function: function_node.left,
                    proof: argument,
                },
            );
        }
        if argument_is_refl {
            return self.alloc(
                left,
                right,
                EGraphProofKind::CongFunction {
                    argument: argument_node.left,
                    proof: function,
                },
            );
        }
        self.alloc(left, right, EGraphProofKind::CongApp(function, argument))
    }

    fn congr_terms(&mut self, function: ProofId, argument: ProofId) -> ProofId {
        let (fl, fr) = {
            let n = &self.proofs[function.0 as usize];
            (n.left, n.right)
        };
        let (al, ar) = {
            let n = &self.proofs[argument.0 as usize];
            (n.left, n.right)
        };
        let left = self.app_term(fl, al);
        let right = self.app_term(fr, ar);
        self.congr_terms_with_endpoints(left, right, function, argument)
    }

    fn rewrite(
        &mut self,
        left: PlacedTerm,
        right: PlacedTerm,
        name: String,
        arguments: Vec<PlacedTerm>,
    ) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Rewrite { name, arguments })
    }

    fn raw_app_to(
        &mut self,
        trace: &EGraphProofTrace,
        raw: Id,
        function: Id,
        argument: Id,
    ) -> Option<ProofId> {
        let EGraphTermDefinition::App(old_function, old_argument) = trace.definition(raw.raw())?
        else {
            return None;
        };
        let fp = self.proof_between(trace, old_function, function);
        let ap = self.proof_between(trace, old_argument, argument);
        let old_function = self.placed(old_function);
        let old_argument = self.placed(old_argument);
        let definition = self.app_term(old_function, old_argument);
        let raw = self.placed(raw);
        let unfold = self.refl_terms(raw, definition);
        let normalize = self.congr_terms(fp, ap);
        Some(self.trans(unfold, normalize))
    }

    fn materialize_reason(&mut self, trace: &EGraphProofTrace, reason: ReasonId) -> ProofId {
        if let Some(proof) = self.materialized_reasons[reason.0 as usize] {
            return proof;
        }
        let node = trace.reasons[reason.0 as usize].clone();
        let proof = match node.reason {
            Reason::Definitional => self.refl_between(node.left, node.right),
            Reason::Assumption { index, label } => {
                let left = self.placed(node.left);
                let right = self.placed(node.right);
                self.alloc(left, right, EGraphProofKind::Assumption { index, label })
            }
            Reason::Rewrite {
                rule,
                subst,
                normalization,
            } => {
                let rule = trace.rules[rule.0 as usize].clone();
                let name = rule.name().expect("proof rules are named").to_owned();
                let arguments = rule
                    .metavariables()
                    .iter()
                    .map(|name| {
                        self.placed(*subst.get(name).expect("complete rewrite substitution"))
                    })
                    .collect();
                if normalization.is_none() {
                    let left = self.placed(node.left);
                    let right = self.placed(node.right);
                    let proof = self.rewrite(left, right, name, arguments);
                    self.materialized_reasons[reason.0 as usize] = Some(proof);
                    return proof;
                }
                let normalization = normalization.unwrap();
                let left_normal = normalization
                    .left
                    .last()
                    .expect("nonempty left pattern")
                    .normal;
                let right_normal = normalization
                    .right
                    .last()
                    .expect("nonempty right pattern")
                    .normal;
                let (left_term, left_normalization) =
                    self.materialize_pattern(trace, rule.lhs(), &normalization.left);
                let (right_term, right_normalization) =
                    self.materialize_pattern(trace, rule.rhs(), &normalization.right);
                let target_path = self.proof_between(trace, node.left, left_normal);
                let left_back = self.symm(left_normalization);
                let proof = self.trans(target_path, left_back);
                let rewrite = self.rewrite(left_term, right_term, name, arguments);
                let proof = self.trans(proof, rewrite);
                let proof = self.trans(proof, right_normalization);
                let replacement_path = self.proof_between(trace, node.right, right_normal);
                let replacement_back = self.symm(replacement_path);
                self.trans(proof, replacement_back)
            }
            Reason::Congruence {
                left_function,
                right_function,
                left_argument,
                right_argument,
            } => {
                // These pairs were already equivalent before this reason's forest edge was
                // inserted. Later successful unions only attach other trees, so their unique
                // paths cannot acquire this edge and recursive explanation remains acyclic.
                let function = self.proof_between(trace, left_function, right_function);
                let argument = self.proof_between(trace, left_argument, right_argument);
                self.congr_app(node.left, node.right, function, argument)
            }
            Reason::RootEquality {
                direct,
                input_left,
                input_right,
                left_root,
                right_root,
            } => {
                let direct = self.materialize_reason(trace, direct);
                let left_to_root = self.proof_between(trace, input_left, left_root);
                let right_to_root = self.proof_between(trace, input_right, right_root);
                let root_to_left = self.symm(left_to_root);
                let proof = self.trans(root_to_left, direct);
                self.trans(proof, right_to_root)
            }
            Reason::SpecializeLeft { equality, left } => {
                let equality = self.materialize_reason(trace, equality);
                let left_endpoint = self.placed(node.left);
                let right_endpoint = self.placed(node.right);
                self.alloc(
                    left_endpoint,
                    right_endpoint,
                    EGraphProofKind::SpecializeLeft { equality, left },
                )
            }
            Reason::SpecializeRight { equality, right } => {
                let equality = self.materialize_reason(trace, equality);
                let left_endpoint = self.placed(node.left);
                let right_endpoint = self.placed(node.right);
                self.alloc(
                    left_endpoint,
                    right_endpoint,
                    EGraphProofKind::SpecializeRight { equality, right },
                )
            }
            Reason::FactorLeft {
                equality,
                left,
                common,
            } => {
                let equality = self.materialize_reason(trace, equality);
                let left_endpoint = self.placed(node.left);
                let right_endpoint = self.placed(node.right);
                self.alloc(
                    left_endpoint,
                    right_endpoint,
                    EGraphProofKind::FactorLeft {
                        equality,
                        left,
                        common,
                    },
                )
            }
            Reason::FactorRight { equality, right } => {
                let equality = self.materialize_reason(trace, equality);
                let left_endpoint = self.placed(node.left);
                let right_endpoint = self.placed(node.right);
                self.alloc(
                    left_endpoint,
                    right_endpoint,
                    EGraphProofKind::FactorRight { equality, right },
                )
            }
        };
        self.materialized_reasons[reason.0 as usize] = Some(proof);
        proof
    }

    fn materialize_pattern(
        &mut self,
        trace: &EGraphProofTrace,
        pattern: &Pattern,
        witnesses: &[PatternNodeWitness],
    ) -> (PlacedTerm, ProofId) {
        fn go(
            arena: &mut EGraphProofArena,
            trace: &EGraphProofTrace,
            pattern: &Pattern,
            witnesses: &mut std::slice::Iter<'_, PatternNodeWitness>,
        ) -> (PlacedTerm, ProofId, Id) {
            match pattern {
                Pattern::MetaVar(_, _) | Pattern::Atom(_) => {
                    let witness = witnesses.next().expect("pattern leaf witness");
                    let term = arena.placed(witness.raw);
                    let proof = arena.proof_between(trace, witness.raw, witness.normal);
                    (term, proof, witness.normal)
                }
                Pattern::App(function, argument) => {
                    let (function_term, function_proof, function_normal) =
                        go(arena, trace, function, witnesses);
                    let (argument_term, argument_proof, argument_normal) =
                        go(arena, trace, argument, witnesses);
                    let witness = witnesses.next().expect("application witness");
                    let expression = arena.app_term(function_term, argument_term);
                    let expression_to_normal = arena.congr_terms(function_proof, argument_proof);
                    let witness_to_normal = arena
                        .raw_app_to(trace, witness.raw, function_normal, argument_normal)
                        .expect("an application pattern retains an application witness");
                    let normal_to_witness = arena.symm(witness_to_normal);
                    let expression_to_witness =
                        arena.trans(expression_to_normal, normal_to_witness);
                    let witness_to_root = arena.proof_between(trace, witness.raw, witness.normal);
                    let proof = arena.trans(expression_to_witness, witness_to_root);
                    (expression, proof, witness.normal)
                }
                _ => {
                    unreachable!("proof rules contain only atoms, metavariables, and applications")
                }
            }
        }

        let mut witnesses = witnesses.iter();
        let (term, proof, _) = go(self, trace, pattern, &mut witnesses);
        assert!(witnesses.next().is_none(), "one witness per pattern node");
        (term, proof)
    }

    fn plan_path(start: Id, path: &[ExplainEdge]) -> Vec<PartialLift> {
        let mut maps = vec![PartialLift::total(start.lift())];
        for &edge in path {
            let current = maps.last().unwrap();
            let next = if edge.reversed {
                PartialLift::total(edge.thinning).reverse().then(current)
            } else {
                PartialLift::total(edge.thinning).then(current)
            };
            maps.push(next);
        }
        maps
    }

    fn complete_path(maps: &mut [PartialLift], edges: &[ExplainEdge]) {
        for index in (0..edges.len()).rev() {
            let edge = edges[index];
            let required = if edge.reversed {
                PartialLift::total(edge.thinning).then(&maps[index + 1])
            } else {
                PartialLift::total(edge.thinning)
                    .reverse()
                    .then(&maps[index + 1])
            };
            maps[index] = maps[index].merge(&required);
        }
    }

    fn materialize_path(
        &mut self,
        trace: &EGraphProofTrace,
        start: Id,
        path: &[ExplainEdge],
        maps: &[PartialLift],
    ) -> ProofId {
        let endpoint = self.placed(Id::new(maps[0].finish(), start.raw()));
        let mut proof = self.alloc(endpoint, endpoint, EGraphProofKind::Refl);
        for (index, &edge) in path.iter().enumerate() {
            let step = self.materialize_reason(trace, edge.reason);
            let step = if edge.reversed {
                let lifted = self.lift_proof(step, maps[index + 1].finish());
                self.symm(lifted)
            } else {
                self.lift_proof(step, maps[index].finish())
            };
            proof = self.trans(proof, step);
        }
        proof
    }

    fn proof_between(&mut self, trace: &EGraphProofTrace, left: Id, right: Id) -> ProofId {
        assert_eq!(left.ctx(), right.ctx());
        if self.materialized_reasons.len() < trace.reasons.len() {
            self.materialized_reasons.resize(trace.reasons.len(), None);
        }
        let (left_path, right_path) = trace.explanation_paths(left.raw(), right.raw());
        let mut left_maps = Self::plan_path(left, &left_path);
        let mut right_maps = Self::plan_path(right, &right_path);
        let common = left_maps.last().unwrap().merge(right_maps.last().unwrap());
        *left_maps.last_mut().unwrap() = common;
        *right_maps.last_mut().unwrap() = common;
        Self::complete_path(&mut left_maps, &left_path);
        Self::complete_path(&mut right_maps, &right_path);
        let left_to_common = self.materialize_path(trace, left, &left_path, &left_maps);
        let right_to_common = self.materialize_path(trace, right, &right_path, &right_maps);
        let common_to_right = self.symm(right_to_common);
        self.trans(left_to_common, common_to_right)
    }

    fn live_from(&self, conclusion: ProofId) -> Vec<bool> {
        let mut live = vec![false; self.proofs.len()];
        let mut work = vec![conclusion];
        while let Some(proof) = work.pop() {
            let index = proof.0 as usize;
            if std::mem::replace(&mut live[index], true) {
                continue;
            }
            match self.proofs[index].kind {
                EGraphProofKind::Refl | EGraphProofKind::Assumption { .. } => {}
                EGraphProofKind::Rewrite { .. } => {}
                EGraphProofKind::Symm(child) | EGraphProofKind::Lift { proof: child, .. } => {
                    work.push(child)
                }
                EGraphProofKind::CongFunction { proof, .. }
                | EGraphProofKind::CongArgument { proof, .. } => work.push(proof),
                EGraphProofKind::Trans(left, right) | EGraphProofKind::CongApp(left, right) => {
                    work.push(left);
                    work.push(right);
                }
                EGraphProofKind::SpecializeLeft { equality, .. }
                | EGraphProofKind::SpecializeRight { equality, .. }
                | EGraphProofKind::FactorLeft { equality, .. }
                | EGraphProofKind::FactorRight { equality, .. } => work.push(equality),
            }
        }
        live
    }

    fn mark_endpoint(
        &self,
        trace: &EGraphProofTrace,
        endpoint: PlacedTerm,
        live_terms: &mut [bool],
    ) -> Result<(), ProofError> {
        match self.terms[endpoint.term.0 as usize] {
            EGraphTermNode::Raw(raw) => trace.mark_term(raw, live_terms),
            EGraphTermNode::App(function, argument) => {
                self.mark_endpoint(trace, function, live_terms)?;
                self.mark_endpoint(trace, argument, live_terms)
            }
        }
    }

    fn term_value(
        &self,
        trace: &EGraphProofTrace,
        endpoint: PlacedTerm,
        local: bool,
    ) -> Result<String, ProofError> {
        match self.terms[endpoint.term.0 as usize] {
            EGraphTermNode::Raw(raw) => {
                let source = if local {
                    format!("e{raw}")
                } else {
                    trace.source_term(raw)?
                };
                Ok(EGraphProofTrace::apply(
                    &format!("({source})"),
                    &EGraphProofTrace::selected_arguments(endpoint.lift),
                ))
            }
            EGraphTermNode::App(function, argument) => {
                let function = Self::lift_term(function, endpoint.lift);
                let argument = Self::lift_term(argument, endpoint.lift);
                Ok(format!(
                    "({}) ({})",
                    self.term_value(trace, function, local)?,
                    self.term_value(trace, argument, local)?
                ))
            }
        }
    }

    fn relation_type(
        &self,
        trace: &EGraphProofTrace,
        left: PlacedTerm,
        right: PlacedTerm,
        local: bool,
    ) -> Result<String, ProofError> {
        let arity = left.lift.cod();
        assert_eq!(arity, right.lift.cod());
        let equality = format!(
            "{} = {}",
            self.term_value(trace, left, local)?,
            self.term_value(trace, right, local)?
        );
        Ok(if arity == 0 {
            equality
        } else {
            format!(
                "∀ ({} : α), {equality}",
                EGraphProofTrace::variables(arity).join(" ")
            )
        })
    }

    fn definition_expression(
        &self,
        trace: &EGraphProofTrace,
        raw: RawId,
    ) -> Result<String, ProofError> {
        match trace.definitions[raw as usize].as_ref() {
            Some(EGraphTermDefinition::Atom(name)) => Ok(name.clone()),
            Some(EGraphTermDefinition::Var) => Ok("fun x0 : α => x0".to_owned()),
            Some(EGraphTermDefinition::App(function, argument)) => {
                let local_value = |id: Id| {
                    EGraphProofTrace::apply(
                        &format!("(e{})", id.raw()),
                        &EGraphProofTrace::selected_arguments(id.lift()),
                    )
                };
                let body = format!("({}) ({})", local_value(*function), local_value(*argument));
                Ok(EGraphProofTrace::lambda(
                    trace.contexts[raw as usize],
                    &body,
                ))
            }
            Some(EGraphTermDefinition::Restrict { source, thinning }) => {
                let body = EGraphProofTrace::apply(
                    &format!("e{source}"),
                    &EGraphProofTrace::filled_arguments(*thinning),
                );
                Ok(EGraphProofTrace::lambda(thinning.dom(), &body))
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn apply_proof(proof: ProofId, arguments: &[String]) -> String {
        if arguments.is_empty() {
            format!("p{}", proof.0)
        } else {
            format!("(p{} {})", proof.0, arguments.join(" "))
        }
    }

    fn pointwise(arity: usize, body: String) -> String {
        if arity == 0 {
            body
        } else {
            format!(
                "fun {} => {body}",
                EGraphProofTrace::variables(arity).join(" ")
            )
        }
    }

    fn render(
        &self,
        trace: &EGraphProofTrace,
        theorem_name: &str,
        binders: &str,
        left: Id,
        right: Id,
        conclusion: ProofId,
    ) -> Result<String, ProofError> {
        if let Some(message) = &trace.unsupported {
            return Err(ProofError::Unsupported(message.clone()));
        }
        let live = self.live_from(conclusion);
        let conclusion_node = &self.proofs[conclusion.0 as usize];
        let mut output = format!("theorem {theorem_name} {binders}");
        for (is_live, node) in live.iter().zip(&self.proofs) {
            if *is_live && let EGraphProofKind::Assumption { index, .. } = node.kind {
                output.push_str(&format!(
                    " (h{index} : {})",
                    self.relation_type(trace, node.left, node.right, false)?
                ));
            }
        }
        output.push_str(&format!(
            " : {} := by\n",
            self.relation_type(trace, conclusion_node.left, conclusion_node.right, false)?
        ));

        let mut live_terms = vec![false; trace.definitions.len()];
        trace.mark_term(left.raw(), &mut live_terms)?;
        trace.mark_term(right.raw(), &mut live_terms)?;
        for (is_live, node) in live.iter().zip(&self.proofs) {
            if *is_live {
                self.mark_endpoint(trace, node.left, &mut live_terms)?;
                self.mark_endpoint(trace, node.right, &mut live_terms)?;
                if let EGraphProofKind::Rewrite { ref arguments, .. } = node.kind {
                    for &argument in arguments {
                        self.mark_endpoint(trace, argument, &mut live_terms)?;
                    }
                }
            }
        }
        for (raw, is_live) in live_terms.into_iter().enumerate() {
            if !is_live {
                continue;
            }
            let expression = self.definition_expression(trace, raw as RawId)?;
            output.push_str(&format!("  let e{raw} := {expression}\n"));
        }
        for (index, node) in self.proofs.iter().enumerate() {
            if !live[index] {
                continue;
            }
            let expression = match node.kind {
                EGraphProofKind::Refl => Self::pointwise(node.left.lift.cod(), "rfl".to_owned()),
                EGraphProofKind::Symm(proof) => {
                    let arguments = EGraphProofTrace::variables(node.left.lift.cod());
                    Self::pointwise(
                        arguments.len(),
                        format!("Eq.symm ({})", Self::apply_proof(proof, &arguments)),
                    )
                }
                EGraphProofKind::Trans(first, second) => {
                    let arguments = EGraphProofTrace::variables(node.left.lift.cod());
                    Self::pointwise(
                        arguments.len(),
                        format!(
                            "Eq.trans ({}) ({})",
                            Self::apply_proof(first, &arguments),
                            Self::apply_proof(second, &arguments)
                        ),
                    )
                }
                EGraphProofKind::Lift { proof, lift } => Self::pointwise(
                    lift.cod(),
                    Self::apply_proof(proof, &EGraphProofTrace::selected_arguments(lift)),
                ),
                EGraphProofKind::CongApp(function, argument) => {
                    let arguments = EGraphProofTrace::variables(node.left.lift.cod());
                    Self::pointwise(
                        arguments.len(),
                        format!(
                            "congr ({}) ({})",
                            Self::apply_proof(function, &arguments),
                            Self::apply_proof(argument, &arguments)
                        ),
                    )
                }
                EGraphProofKind::CongFunction { argument, proof } => {
                    let arguments = EGraphProofTrace::variables(node.left.lift.cod());
                    Self::pointwise(
                        arguments.len(),
                        format!(
                            "congrFun ({}) ({})",
                            Self::apply_proof(proof, &arguments),
                            self.term_value(trace, argument, true)?
                        ),
                    )
                }
                EGraphProofKind::CongArgument { function, proof } => {
                    let arguments = EGraphProofTrace::variables(node.left.lift.cod());
                    Self::pointwise(
                        arguments.len(),
                        format!(
                            "congrArg ({}) ({})",
                            self.term_value(trace, function, true)?,
                            Self::apply_proof(proof, &arguments)
                        ),
                    )
                }
                EGraphProofKind::Rewrite {
                    ref name,
                    ref arguments,
                } => {
                    let arity = node.left.lift.cod();
                    let values = arguments
                        .iter()
                        .map(|&argument| self.term_value(trace, argument, true))
                        .collect::<Result<Vec<_>, _>>()?;
                    Self::pointwise(arity, EGraphProofTrace::apply(name, &values))
                }
                EGraphProofKind::SpecializeLeft { equality, left } => Self::pointwise(
                    left.dom(),
                    Self::apply_proof(equality, &EGraphProofTrace::filled_arguments(left)),
                ),
                EGraphProofKind::SpecializeRight { equality, right } => Self::pointwise(
                    right.dom(),
                    format!(
                        "Eq.symm ({})",
                        Self::apply_proof(equality, &EGraphProofTrace::filled_arguments(right))
                    ),
                ),
                EGraphProofKind::FactorLeft {
                    equality,
                    left,
                    common,
                } => {
                    let original =
                        Self::apply_proof(equality, &EGraphProofTrace::filled_arguments(left));
                    let restricted = Self::apply_proof(
                        equality,
                        &EGraphProofTrace::subset_arguments(left, common),
                    );
                    Self::pointwise(
                        left.dom(),
                        format!("Eq.trans ({original}) (Eq.symm ({restricted}))"),
                    )
                }
                EGraphProofKind::FactorRight { equality, right } => Self::pointwise(
                    right.dom(),
                    format!(
                        "Eq.symm ({})",
                        Self::apply_proof(equality, &EGraphProofTrace::filled_arguments(right))
                    ),
                ),
                EGraphProofKind::Assumption { index, ref label } => {
                    output.push_str(&format!("  -- {label}\n"));
                    format!("h{index}")
                }
            };
            output.push_str(&format!(
                "  let p{index} : {} := {expression}\n",
                self.relation_type(trace, node.left, node.right, true)?
            ));
        }
        output.push_str(&format!("  exact p{}\n", conclusion.0));
        Ok(output)
    }
}

impl std::error::Error for ProofError {}

/// Errors returned when asking a proof-disabled or disconnected union-find for a certificate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProofError {
    TrackingDisabled,
    UnknownName(String),
    NotEquivalent { left: String, right: String },
    Unsupported(String),
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TrackingDisabled => write!(formatter, "proof tracking is disabled"),
            Self::UnknownName(name) => write!(formatter, "unknown term {name:?}"),
            Self::NotEquivalent { left, right } => {
                write!(formatter, "{left:?} and {right:?} are not equivalent")
            }
            Self::Unsupported(message) => {
                write!(formatter, "unsupported proof operation: {message}")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::process::{Command, Stdio};

    fn next_random(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    fn random_below(state: &mut u64, limit: usize) -> usize {
        (next_random(state) as usize) % limit
    }

    #[test]
    fn egraph_rebuild_emits_a_lean_checked_congruence_proof() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let f = egraph.atom("f", 0);
        let a = egraph.atom("a", 0);
        let b = egraph.atom("b", 0);
        let fa = egraph.app(f, a);
        let fb = egraph.app(f, b);
        let c = egraph.atom("c", 0);
        let d = egraph.atom("d", 0);
        egraph.union_assuming(&a, &b, "input equality a = b");
        egraph.union_assuming(&c, &d, "irrelevant equality c = d");
        egraph.rebuild();
        assert_eq!(egraph.proof_stats().unwrap().explanation_reasons, 3);

        let certificate = egraph
            .lean_proof(
                "first_order_congruence",
                "{α : Type} (f : α → α) (a b : α)",
                &fa,
                &fb,
            )
            .unwrap();
        assert!(certificate.contains("congrArg"), "{certificate}");
        assert!(!certificate.contains("irrelevant equality"));
        assert!(!certificate.contains("let e5"));
        assert_eq!(certificate.matches("input equality a = b").count(), 1);

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected the generated e-graph certificate:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn egraph_dependency_pruning_emits_a_lean_checked_pointwise_proof() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let f = egraph.atom("f", 1);
        let z = egraph.var(1, 0);
        let f_z = egraph.app(f, z);
        let g = egraph.atom("g", 1);
        let g_z = egraph.app(g, z);

        let f = egraph.atom("f", 2);
        let x = egraph.var(2, 0);
        let f_x = egraph.app(f, x);
        let g = egraph.atom("g", 2);
        let y = egraph.var(2, 1);
        let g_y = egraph.app(g, y);
        assert!(egraph.union_assuming(&f_x, &g_y, "f(x) equals g(y)"));
        assert!(egraph.equivalent(&f_z, &g_z));

        let certificate = egraph
            .lean_proof(
                "egraph_dependency_pruning",
                "{α : Type} [Inhabited α] (f g : α → α)",
                &f_z,
                &g_z,
            )
            .unwrap();
        assert!(certificate.contains("h0 : ∀ (x0 x1 : α)"), "{certificate}");
        assert!(certificate.contains(" : ∀ (x0 : α)"), "{certificate}");
        assert!(certificate.contains("default"));

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected the contextual e-graph certificate:\n{certificate}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn egraph_contextual_congruence_checks_in_lean() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let f = egraph.atom("f", 0);
        let g = egraph.atom("g", 0);
        let f_in_context = egraph.atom("f", 1);
        let g_in_context = egraph.atom("g", 1);
        let x = egraph.var(1, 0);
        let f_x = egraph.app(f_in_context, x);
        let g_x = egraph.app(g_in_context, x);
        assert!(egraph.union_assuming(&f, &g, "f equals g"));
        egraph.rebuild();
        assert!(egraph.equivalent(&f_x, &g_x));

        let certificate = egraph
            .lean_proof(
                "contextual_congruence",
                "{α : Type} (f g : α → α)",
                &f_x,
                &g_x,
            )
            .unwrap();
        assert!(certificate.contains("∀ (x0 : α)"), "{certificate}");
        assert!(certificate.contains("congrFun"), "{certificate}");

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected contextual congruence:\n{certificate}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn deterministic_randomized_egraph_thinning_certificates_check_in_lean() {
        const SEED: u64 = 0xe6a9_5eed_cafe_babe;
        const CASES: usize = 8;
        const TERMS: usize = 6;

        let mut state = SEED;
        let mut certificates = String::new();
        for case in 0..CASES {
            let mut egraph = crate::EGraph::new_with_proofs();
            let variable = egraph.var(1, 0);
            let mut terms = Vec::new();
            let mut names = Vec::new();
            for index in 0..TERMS {
                let name = format!("f{index}");
                let function = egraph.atom(&name, 1);
                terms.push(egraph.app(function, variable));
                names.push(name);
            }

            let mut order = (0..TERMS).collect::<Vec<_>>();
            for index in 0..TERMS {
                let selected = index + random_below(&mut state, TERMS - index);
                order.swap(index, selected);
            }
            for step in 1..TERMS {
                let ambient = 1 + random_below(&mut state, 4);
                let left = crate::Id::new(
                    crate::Lift::select(ambient, random_below(&mut state, ambient)),
                    terms[order[step - 1]].raw(),
                );
                let right = crate::Id::new(
                    crate::Lift::select(ambient, random_below(&mut state, ambient)),
                    terms[order[step]].raw(),
                );
                egraph.union_assuming(&left, &right, format!("case {case}, tree {step}"));
            }
            for step in 0..12 {
                let left_index = random_below(&mut state, TERMS);
                let mut right_index = random_below(&mut state, TERMS - 1);
                if right_index >= left_index {
                    right_index += 1;
                }
                let ambient = 1 + random_below(&mut state, 4);
                let left = crate::Id::new(
                    crate::Lift::select(ambient, random_below(&mut state, ambient)),
                    terms[left_index].raw(),
                );
                let right = crate::Id::new(
                    crate::Lift::select(ambient, random_below(&mut state, ambient)),
                    terms[right_index].raw(),
                );
                egraph.union_assuming(&left, &right, format!("case {case}, extra {step}"));
            }

            let left_index = random_below(&mut state, TERMS);
            let mut right_index = random_below(&mut state, TERMS - 1);
            if right_index >= left_index {
                right_index += 1;
            }
            assert!(egraph.equivalent(&terms[left_index], &terms[right_index]));
            certificates.push_str(
                &egraph
                    .lean_proof(
                        &format!("random_egraph_thinning_{case}"),
                        &format!("{{α : Type}} [Inhabited α] ({} : α → α)", names.join(" ")),
                        &terms[left_index],
                        &terms[right_index],
                    )
                    .unwrap(),
            );
            certificates.push('\n');
        }

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificates.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected randomized e-graph certificates (seed {SEED:#x}):\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn egraph_congruence_can_change_both_application_children() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let f = egraph.atom("f", 0);
        let g = egraph.atom("g", 0);
        let a = egraph.atom("a", 0);
        let b = egraph.atom("b", 0);
        let fa = egraph.app(f, a);
        let gb = egraph.app(g, b);
        egraph.union_assuming(&f, &g, "f = g");
        egraph.union_assuming(&a, &b, "a = b");
        let certificate = egraph
            .lean_proof(
                "two_child_congruence",
                "{α β : Type} (f g : α → β) (a b : α)",
                &fa,
                &gb,
            )
            .unwrap();
        assert!(!certificate.contains("congrArg₂"));

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected two-child congruence:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn egraph_congruence_can_change_only_the_function() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let f = egraph.atom("f", 0);
        let g = egraph.atom("g", 0);
        let a = egraph.atom("a", 0);
        let fa = egraph.app(f, a);
        let ga = egraph.app(g, a);
        egraph.union_assuming(&f, &g, "f = g");
        let certificate = egraph
            .lean_proof(
                "function_congruence",
                "{α β : Type} (f g : α → β) (a : α)",
                &fa,
                &ga,
            )
            .unwrap();
        assert!(certificate.contains("congrFun"));

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected function congruence:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn named_rewrite_records_only_a_union_that_changes_the_graph() {
        let mut egraph = crate::EGraph::new_with_proofs();
        let x = egraph.atom("x", 0);
        let zero = egraph.atom("zero", 0);
        let inner = egraph.apps("plus", vec![x, zero]);
        let outer = egraph.apps("plus", vec![inner, zero]);
        let rule = crate::Rewrite::named(
            "r1",
            crate::Pattern::apps(
                "plus",
                vec![crate::Pattern::meta("?a"), crate::Pattern::atom("zero")],
            ),
            crate::Pattern::meta("?a"),
        )
        .unwrap();
        egraph.saturate(std::slice::from_ref(&rule));
        let settled_reasons = egraph.proof_stats().unwrap().explanation_reasons;
        egraph.saturate(std::slice::from_ref(&rule));
        assert_eq!(
            egraph.proof_stats().unwrap().explanation_reasons,
            settled_reasons
        );

        let certificate = egraph
            .lean_proof(
                "two_rewrites",
                "{α : Type} (plus : α → α → α) (zero x : α) \
                 (r1 : ∀ a, plus a zero = a)",
                &outer,
                &x,
            )
            .unwrap();
        assert_eq!(certificate.matches(":= r1 (").count(), 2, "{certificate}");
        assert!(!certificate.contains("simpa"));
        assert!(!certificate.contains("  let t"));
        assert!(!certificate.contains(" := rfl"));

        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected the named rewrite certificate:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
