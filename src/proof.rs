use rustc_hash::FxHashMap as HashMap;

use crate::RawId;

/// An index into the proof-expression arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofId(u32);

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct EGraphProofStats {
    pub steps: usize,
    pub refl: usize,
    pub symm: usize,
    pub trans: usize,
    pub congruence: usize,
    pub rewrites: usize,
    pub assumptions: usize,
    pub expression_terms: usize,
    pub explanation_edges: usize,
    pub explanation_reasons: usize,
}

type Id = u32;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Endpoint {
    Named(String),
    Id(Id),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ProofKind {
    Refl,
    Symm(ProofId),
    Trans(ProofId, ProofId),
    Assumption { index: usize, label: String },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProofNode {
    left: Endpoint,
    right: Endpoint,
    kind: ProofKind,
}

/// One directed edge in the explanation forest.
///
/// `reason` is the equality supplied to the successful union. `reversed` says that the forest
/// edge is currently directed opposite to that equality. Rerooting only flips this bit; it does
/// not eagerly allocate `Eq.symm` nodes in the proof arena.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExplainEdge {
    reason: ProofId,
    reversed: bool,
}

#[derive(Clone, Debug, Default)]
struct ProofState {
    arena: Vec<ProofNode>,
    /// The separate, uncompressed proof forest used to select explanations.
    explain_parents: Vec<Id>,
    /// The equality justifying each edge to `explain_parents`; roots have no edge.
    explain_edges: Vec<Option<ExplainEdge>>,
    /// Proof that each named term equals the e-class allocated for it.
    memo_proofs: HashMap<String, ProofId>,
    assumptions: usize,
}

impl ProofState {
    fn alloc(&mut self, left: Endpoint, right: Endpoint, kind: ProofKind) -> ProofId {
        assert!(self.arena.len() <= u32::MAX as usize, "exhausted proof IDs");
        let id = ProofId(self.arena.len() as u32);
        self.arena.push(ProofNode { left, right, kind });
        id
    }

    fn symm(&mut self, proof: ProofId) -> ProofId {
        let node = &self.arena[proof.0 as usize];
        if node.left == node.right && matches!(node.kind, ProofKind::Refl) {
            return proof;
        }
        self.alloc(
            node.right.clone(),
            node.left.clone(),
            ProofKind::Symm(proof),
        )
    }

    fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        let left_node = &self.arena[left.0 as usize];
        let right_node = &self.arena[right.0 as usize];
        assert_eq!(
            left_node.right, right_node.left,
            "ill-typed transitivity in proof arena"
        );
        if left_node.left == left_node.right && matches!(left_node.kind, ProofKind::Refl) {
            return right;
        }
        if right_node.left == right_node.right && matches!(right_node.kind, ProofKind::Refl) {
            return left;
        }
        self.alloc(
            left_node.left.clone(),
            right_node.right.clone(),
            ProofKind::Trans(left, right),
        )
    }

    fn assumption(&mut self, left: Id, right: Id, label: String) -> ProofId {
        let index = self.assumptions;
        self.assumptions += 1;
        self.alloc(
            Endpoint::Id(left),
            Endpoint::Id(right),
            ProofKind::Assumption { index, label },
        )
    }

    fn reroot_explanation(&mut self, node: Id) {
        let mut current = node;
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
                reversed: !current_edge.reversed,
            });
            current = parent;
            parent = next_parent;
            edge = next_edge;
        }
    }

    fn link_explanations(&mut self, child: Id, parent: Id, reason: ProofId, reversed: bool) {
        self.reroot_explanation(child);
        debug_assert_eq!(self.explain_parents[child as usize], child);
        debug_assert!(self.explain_edges[child as usize].is_none());
        self.explain_parents[child as usize] = parent;
        self.explain_edges[child as usize] = Some(ExplainEdge { reason, reversed });
    }

    fn oriented_edge(&mut self, edge: ExplainEdge) -> ProofId {
        if edge.reversed {
            self.symm(edge.reason)
        } else {
            edge.reason
        }
    }

    fn explanation_paths(&self, left: Id, right: Id) -> (Vec<ExplainEdge>, Vec<ExplainEdge>) {
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
                "equivalent entries must share an explanation root"
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

    fn live_from(&self, conclusion: ProofId) -> Vec<bool> {
        let mut live = vec![false; self.arena.len()];
        let mut work = vec![conclusion];
        while let Some(proof) = work.pop() {
            let index = proof.0 as usize;
            if std::mem::replace(&mut live[index], true) {
                continue;
            }
            match self.arena[index].kind {
                ProofKind::Refl | ProofKind::Assumption { .. } => {}
                ProofKind::Symm(child) => work.push(child),
                ProofKind::Trans(left, right) => {
                    work.push(left);
                    work.push(right);
                }
            }
        }
        live
    }
}

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EGraphProofTerm {
    Atom(String),
    App(RawId, RawId),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphProofKind {
    Refl,
    Symm(ProofId),
    Trans(ProofId, ProofId),
    CongApp(ProofId, ProofId),
    CongFunction {
        argument: EGraphTermId,
        proof: ProofId,
    },
    CongArgument {
        function: EGraphTermId,
        proof: ProofId,
    },
    Rewrite {
        name: String,
        arguments: Vec<RawId>,
    },
    Assumption {
        index: usize,
        label: String,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct EGraphProofNode {
    left: EGraphTermId,
    right: EGraphTermId,
    kind: EGraphProofKind,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) struct EGraphTermId(u32);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphTermNode {
    Raw(RawId),
    App(EGraphTermId, EGraphTermId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EGraphReasonId(u32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EGraphReasonUse {
    reason: EGraphReasonId,
    reversed: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct EGraphExplanationPath {
    left: RawId,
    right: RawId,
    reasons: Vec<EGraphReasonUse>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphReasonKind {
    Direct(ProofId),
    RewriteDirect {
        name: String,
        arguments: Vec<RawId>,
    },
    Rewrite {
        name: String,
        arguments: Vec<RawId>,
        left: EGraphPatternRecipe,
        right: EGraphPatternRecipe,
    },
    Congruence {
        left_function: RawId,
        right_function: RawId,
        left_argument: RawId,
        right_argument: RawId,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum EGraphPatternRecipe {
    Raw {
        raw: RawId,
        normal: RawId,
    },
    App {
        witness: RawId,
        normal: RawId,
        function: Box<EGraphPatternRecipe>,
        argument: Box<EGraphPatternRecipe>,
    },
}

impl EGraphPatternRecipe {
    fn normal(&self) -> RawId {
        match self {
            Self::Raw { normal, .. } | Self::App { normal, .. } => *normal,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct EGraphReasonNode {
    left: RawId,
    right: RawId,
    kind: EGraphReasonKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct EGraphExplainEdge {
    reason: EGraphReasonId,
    reversed: bool,
}

#[derive(Clone, Debug)]
pub(crate) enum EGraphUnionReason {
    Direct(ProofId),
    RewriteDirect {
        name: String,
        arguments: Vec<RawId>,
    },
    Rewrite {
        name: String,
        arguments: Vec<RawId>,
        left: EGraphPatternRecipe,
        right: EGraphPatternRecipe,
    },
    Congruence {
        left_function: RawId,
        right_function: RawId,
        left_argument: RawId,
        right_argument: RawId,
    },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EGraphProofState {
    arena: Vec<EGraphProofNode>,
    proof_memo: HashMap<EGraphProofNode, ProofId>,
    terms: Vec<EGraphTermNode>,
    term_memo: HashMap<EGraphTermNode, EGraphTermId>,
    raw_terms: Vec<EGraphTermId>,
    definitions: Vec<Option<EGraphProofTerm>>,
    explain_parents: Vec<RawId>,
    explain_edges: Vec<Option<EGraphExplainEdge>>,
    explain_sizes: Vec<usize>,
    reasons: Vec<EGraphReasonNode>,
    materialized_reasons: Vec<Option<ProofId>>,
    assumptions: usize,
    unsupported: Option<String>,
}

impl EGraphProofState {
    pub(crate) fn step_count(&self) -> usize {
        self.arena.len()
    }

    pub(crate) fn stats(&self) -> EGraphProofStats {
        let mut stats = EGraphProofStats {
            steps: self.arena.len(),
            expression_terms: self.terms.len(),
            explanation_edges: self.explain_edges.iter().flatten().count(),
            explanation_reasons: self.reasons.len(),
            ..EGraphProofStats::default()
        };
        for node in &self.arena {
            match node.kind {
                EGraphProofKind::Refl => stats.refl += 1,
                EGraphProofKind::Symm(_) => stats.symm += 1,
                EGraphProofKind::Trans(_, _) => stats.trans += 1,
                EGraphProofKind::CongApp(_, _)
                | EGraphProofKind::CongFunction { .. }
                | EGraphProofKind::CongArgument { .. } => stats.congruence += 1,
                EGraphProofKind::Rewrite { .. } => stats.rewrites += 1,
                EGraphProofKind::Assumption { .. } => stats.assumptions += 1,
            }
        }
        stats
    }

    fn alloc(&mut self, left: EGraphTermId, right: EGraphTermId, kind: EGraphProofKind) -> ProofId {
        let node = EGraphProofNode { left, right, kind };
        if let Some(&proof) = self.proof_memo.get(&node) {
            return proof;
        }
        assert!(self.arena.len() <= u32::MAX as usize, "exhausted proof IDs");
        let proof = ProofId(self.arena.len() as u32);
        self.arena.push(node.clone());
        self.proof_memo.insert(node, proof);
        proof
    }

    pub(crate) fn make_set(&mut self, raw: RawId, context: usize) {
        assert_eq!(self.definitions.len(), raw as usize);
        self.definitions.push(None);
        let term = self.alloc_term(EGraphTermNode::Raw(raw));
        self.raw_terms.push(term);
        self.explain_parents.push(raw);
        self.explain_edges.push(None);
        self.explain_sizes.push(1);
        if context != 0 {
            self.unsupported(format!("e{raw} was allocated in context {context}"));
        }
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

    pub(crate) fn raw_term(&self, raw: RawId) -> EGraphTermId {
        self.raw_terms[raw as usize]
    }

    pub(crate) fn app_term(
        &mut self,
        function: EGraphTermId,
        argument: EGraphTermId,
    ) -> EGraphTermId {
        self.alloc_term(EGraphTermNode::App(function, argument))
    }

    pub(crate) fn define(&mut self, raw: RawId, definition: EGraphProofTerm) {
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

    pub(crate) fn definition(&self, raw: RawId) -> Option<EGraphProofTerm> {
        self.definitions[raw as usize].clone()
    }

    pub(crate) fn refl_between(&mut self, left: RawId, right: RawId) -> ProofId {
        self.refl_terms(self.raw_term(left), self.raw_term(right))
    }

    pub(crate) fn refl_terms(&mut self, left: EGraphTermId, right: EGraphTermId) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Refl)
    }

    pub(crate) fn assumption(&mut self, left: RawId, right: RawId, label: String) -> ProofId {
        let index = self.assumptions;
        self.assumptions += 1;
        self.alloc(
            self.raw_term(left),
            self.raw_term(right),
            EGraphProofKind::Assumption { index, label },
        )
    }

    pub(crate) fn symm(&mut self, proof: ProofId) -> ProofId {
        let node = &self.arena[proof.0 as usize];
        if node.left == node.right && matches!(node.kind, EGraphProofKind::Refl) {
            return proof;
        }
        self.alloc(node.right, node.left, EGraphProofKind::Symm(proof))
    }

    pub(crate) fn trans(&mut self, left: ProofId, right: ProofId) -> ProofId {
        let left_node = &self.arena[left.0 as usize];
        let right_node = &self.arena[right.0 as usize];
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

    pub(crate) fn congr_app(
        &mut self,
        left: RawId,
        right: RawId,
        function: ProofId,
        argument: ProofId,
    ) -> ProofId {
        let left = self.raw_term(left);
        let right = self.raw_term(right);
        self.congr_terms_with_endpoints(left, right, function, argument)
    }

    fn congr_terms_with_endpoints(
        &mut self,
        left: EGraphTermId,
        right: EGraphTermId,
        function: ProofId,
        argument: ProofId,
    ) -> ProofId {
        let function_node = &self.arena[function.0 as usize];
        let argument_node = &self.arena[argument.0 as usize];
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

    pub(crate) fn congr_terms(&mut self, function: ProofId, argument: ProofId) -> ProofId {
        let (fl, fr) = {
            let n = &self.arena[function.0 as usize];
            (n.left, n.right)
        };
        let (al, ar) = {
            let n = &self.arena[argument.0 as usize];
            (n.left, n.right)
        };
        let left = self.app_term(fl, al);
        let right = self.app_term(fr, ar);
        self.congr_terms_with_endpoints(left, right, function, argument)
    }

    pub(crate) fn rewrite(
        &mut self,
        left: EGraphTermId,
        right: EGraphTermId,
        name: String,
        arguments: Vec<RawId>,
    ) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Rewrite { name, arguments })
    }

    pub(crate) fn raw_app_to(
        &mut self,
        raw: RawId,
        function: RawId,
        argument: RawId,
    ) -> Option<ProofId> {
        let EGraphProofTerm::App(old_function, old_argument) = self.definition(raw)? else {
            return None;
        };
        let fp = self.proof_between(old_function, function);
        let ap = self.proof_between(old_argument, argument);
        let definition = self.app_term(self.raw_term(old_function), self.raw_term(old_argument));
        let unfold = self.refl_terms(self.raw_term(raw), definition);
        let normalize = self.congr_terms(fp, ap);
        Some(self.trans(unfold, normalize))
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
            self.explain_edges[parent as usize] = Some(EGraphExplainEdge {
                reason: current_edge.reason,
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

    fn explanation_path(&self, left: RawId, right: RawId) -> EGraphExplanationPath {
        if left == right {
            return EGraphExplanationPath {
                left,
                right,
                reasons: Vec::new(),
            };
        }
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
        let mut reasons = left_edges
            .into_iter()
            .map(|edge| EGraphReasonUse {
                reason: edge.reason,
                reversed: edge.reversed,
            })
            .collect::<Vec<_>>();
        reasons.extend(right_edges.into_iter().rev().map(|edge| EGraphReasonUse {
            reason: edge.reason,
            reversed: !edge.reversed,
        }));
        EGraphExplanationPath {
            left,
            right,
            reasons,
        }
    }

    fn alloc_reason(&mut self, node: EGraphReasonNode) -> EGraphReasonId {
        assert!(
            self.reasons.len() <= u32::MAX as usize,
            "exhausted reason IDs"
        );
        let reason = EGraphReasonId(self.reasons.len() as u32);
        self.reasons.push(node);
        self.materialized_reasons.push(None);
        reason
    }

    pub(crate) fn link_explanation(
        &mut self,
        left: RawId,
        right: RawId,
        reason: EGraphUnionReason,
    ) {
        let left_root = self.explanation_root(left);
        let right_root = self.explanation_root(right);
        assert_ne!(
            left_root, right_root,
            "a proof edge must join two components"
        );
        let kind = match reason {
            EGraphUnionReason::Direct(proof) => {
                debug_assert_eq!(self.arena[proof.0 as usize].left, self.raw_term(left));
                debug_assert_eq!(self.arena[proof.0 as usize].right, self.raw_term(right));
                EGraphReasonKind::Direct(proof)
            }
            EGraphUnionReason::RewriteDirect { name, arguments } => {
                EGraphReasonKind::RewriteDirect { name, arguments }
            }
            EGraphUnionReason::Rewrite {
                name,
                arguments,
                left,
                right,
            } => EGraphReasonKind::Rewrite {
                name,
                arguments,
                left,
                right,
            },
            EGraphUnionReason::Congruence {
                left_function,
                right_function,
                left_argument,
                right_argument,
            } => EGraphReasonKind::Congruence {
                left_function,
                right_function,
                left_argument,
                right_argument,
            },
        };
        let reason = self.alloc_reason(EGraphReasonNode { left, right, kind });

        if self.explain_sizes[left_root as usize] <= self.explain_sizes[right_root as usize] {
            self.reroot_explanation(left);
            let right_root = self.explanation_root(right);
            let left_size = self.explain_sizes[left as usize];
            self.explain_parents[left as usize] = right;
            self.explain_edges[left as usize] = Some(EGraphExplainEdge {
                reason,
                reversed: false,
            });
            self.explain_sizes[left as usize] = 0;
            self.explain_sizes[right_root as usize] += left_size;
        } else {
            self.reroot_explanation(right);
            let left_root = self.explanation_root(left);
            let right_size = self.explain_sizes[right as usize];
            self.explain_parents[right as usize] = left;
            self.explain_edges[right as usize] = Some(EGraphExplainEdge {
                reason,
                reversed: true,
            });
            self.explain_sizes[right as usize] = 0;
            self.explain_sizes[left_root as usize] += right_size;
        }
    }

    fn materialize_reason(&mut self, reason: EGraphReasonId) -> ProofId {
        if let Some(proof) = self.materialized_reasons[reason.0 as usize] {
            return proof;
        }
        let node = self.reasons[reason.0 as usize].clone();
        let proof = match node.kind {
            EGraphReasonKind::Direct(proof) => proof,
            EGraphReasonKind::RewriteDirect { name, arguments } => self.rewrite(
                self.raw_term(node.left),
                self.raw_term(node.right),
                name,
                arguments,
            ),
            EGraphReasonKind::Rewrite {
                name,
                arguments,
                left,
                right,
            } => {
                let left_normal = left.normal();
                let right_normal = right.normal();
                let (left_term, left_normalization) = self.materialize_pattern_recipe(&left);
                let (right_term, right_normalization) = self.materialize_pattern_recipe(&right);
                let target_path = self.proof_between(node.left, left_normal);
                let left_back = self.symm(left_normalization);
                let proof = self.trans(target_path, left_back);
                let rewrite = self.rewrite(left_term, right_term, name, arguments);
                let proof = self.trans(proof, rewrite);
                let proof = self.trans(proof, right_normalization);
                let replacement_path = self.proof_between(node.right, right_normal);
                let replacement_back = self.symm(replacement_path);
                self.trans(proof, replacement_back)
            }
            EGraphReasonKind::Congruence {
                left_function,
                right_function,
                left_argument,
                right_argument,
            } => {
                // These pairs were already equivalent before this reason's forest edge was
                // inserted. Later successful unions only attach other trees, so their unique
                // paths cannot acquire this edge and recursive explanation remains acyclic.
                let function = self.proof_between(left_function, right_function);
                let argument = self.proof_between(left_argument, right_argument);
                self.congr_app(node.left, node.right, function, argument)
            }
        };
        self.materialized_reasons[reason.0 as usize] = Some(proof);
        proof
    }

    fn materialize_pattern_recipe(
        &mut self,
        recipe: &EGraphPatternRecipe,
    ) -> (EGraphTermId, ProofId) {
        match recipe {
            EGraphPatternRecipe::Raw { raw, normal } => {
                let term = self.raw_term(*raw);
                let proof = self.proof_between(*raw, *normal);
                (term, proof)
            }
            EGraphPatternRecipe::App {
                witness,
                normal,
                function,
                argument,
            } => {
                let (function_term, function_proof) = self.materialize_pattern_recipe(function);
                let (argument_term, argument_proof) = self.materialize_pattern_recipe(argument);
                let expression = self.app_term(function_term, argument_term);
                let expression_to_normal = self.congr_terms(function_proof, argument_proof);
                let witness_to_normal = self
                    .raw_app_to(*witness, function.normal(), argument.normal())
                    .expect("a rewrite application recipe retains an application witness");
                let normal_to_witness = self.symm(witness_to_normal);
                let expression_to_witness = self.trans(expression_to_normal, normal_to_witness);
                let witness_to_root = self.proof_between(*witness, *normal);
                let proof = self.trans(expression_to_witness, witness_to_root);
                (expression, proof)
            }
        }
    }

    fn materialize_path(&mut self, path: EGraphExplanationPath) -> ProofId {
        let mut proof = None;
        for reason_use in path.reasons {
            let mut step = self.materialize_reason(reason_use.reason);
            if reason_use.reversed {
                step = self.symm(step);
            }
            proof = Some(match proof {
                Some(prefix) => self.trans(prefix, step),
                None => step,
            });
        }
        proof.unwrap_or_else(|| self.refl_between(path.left, path.right))
    }

    pub(crate) fn proof_between(&mut self, left: RawId, right: RawId) -> ProofId {
        let path = self.explanation_path(left, right);
        self.materialize_path(path)
    }

    fn live_from(&self, conclusion: ProofId) -> Vec<bool> {
        let mut live = vec![false; self.arena.len()];
        let mut work = vec![conclusion];
        while let Some(proof) = work.pop() {
            let index = proof.0 as usize;
            if std::mem::replace(&mut live[index], true) {
                continue;
            }
            match self.arena[index].kind {
                EGraphProofKind::Refl | EGraphProofKind::Assumption { .. } => {}
                EGraphProofKind::Rewrite { .. } => {}
                EGraphProofKind::Symm(child) => work.push(child),
                EGraphProofKind::CongFunction { proof, .. }
                | EGraphProofKind::CongArgument { proof, .. } => work.push(proof),
                EGraphProofKind::Trans(left, right) | EGraphProofKind::CongApp(left, right) => {
                    work.push(left);
                    work.push(right);
                }
            }
        }
        live
    }

    fn source_term(&self, raw: RawId) -> Result<String, ProofError> {
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphProofTerm::Atom(name)) => Ok(name.clone()),
            Some(EGraphProofTerm::App(function, argument)) => {
                let function = self.source_term(*function)?;
                let argument_text = self.source_term(*argument)?;
                let argument = match self.definitions[*argument as usize].as_ref() {
                    Some(EGraphProofTerm::App(_, _)) => format!("({argument_text})"),
                    _ => argument_text,
                };
                Ok(format!("{function} {argument}"))
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn raw_endpoint(&self, term: EGraphTermId) -> Result<RawId, ProofError> {
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => Ok(raw),
            EGraphTermNode::App(_, _) => Err(ProofError::Unsupported(
                "external assumption has a synthetic endpoint".to_owned(),
            )),
        }
    }

    fn term_name(&self, term: EGraphTermId) -> String {
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => format!("e{raw}"),
            EGraphTermNode::App(_, _) => format!("t{}", term.0),
        }
    }

    fn mark_endpoint(
        &self,
        term: EGraphTermId,
        live_terms: &mut [bool],
        live_exprs: &mut [bool],
    ) -> Result<(), ProofError> {
        if std::mem::replace(&mut live_exprs[term.0 as usize], true) {
            return Ok(());
        }
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => self.mark_term(raw, live_terms),
            EGraphTermNode::App(function, argument) => {
                self.mark_endpoint(function, live_terms, live_exprs)?;
                self.mark_endpoint(argument, live_terms, live_exprs)
            }
        }
    }

    fn mark_term(&self, raw: RawId, live: &mut [bool]) -> Result<(), ProofError> {
        if std::mem::replace(&mut live[raw as usize], true) {
            return Ok(());
        }
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphProofTerm::Atom(_)) => Ok(()),
            Some(EGraphProofTerm::App(function, argument)) => {
                self.mark_term(*function, live)?;
                self.mark_term(*argument, live)
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    pub(crate) fn render(
        &self,
        theorem_name: &str,
        binders: &str,
        left: RawId,
        right: RawId,
        conclusion: ProofId,
    ) -> Result<String, ProofError> {
        if let Some(message) = &self.unsupported {
            return Err(ProofError::Unsupported(message.clone()));
        }
        let live = self.live_from(conclusion);
        let mut output = format!("theorem {theorem_name} {binders}");
        for (is_live, node) in live.iter().zip(&self.arena) {
            if *is_live && let EGraphProofKind::Assumption { index, .. } = node.kind {
                let left = self.raw_endpoint(node.left)?;
                let right = self.raw_endpoint(node.right)?;
                output.push_str(&format!(
                    " (h{index} : {} = {})",
                    self.source_term(left)?,
                    self.source_term(right)?
                ));
            }
        }
        output.push_str(&format!(
            " : {} = {} := by\n",
            self.source_term(left)?,
            self.source_term(right)?
        ));

        let mut live_terms = vec![false; self.definitions.len()];
        let mut live_exprs = vec![false; self.terms.len()];
        self.mark_term(left, &mut live_terms)?;
        self.mark_term(right, &mut live_terms)?;
        for (is_live, node) in live.iter().zip(&self.arena) {
            if *is_live {
                self.mark_endpoint(node.left, &mut live_terms, &mut live_exprs)?;
                self.mark_endpoint(node.right, &mut live_terms, &mut live_exprs)?;
                if let EGraphProofKind::Rewrite { ref arguments, .. } = node.kind {
                    for &raw in arguments {
                        self.mark_term(raw, &mut live_terms)?;
                    }
                }
            }
        }
        for (raw, is_live) in live_terms.into_iter().enumerate() {
            if !is_live {
                continue;
            }
            let expression = match self.definitions[raw].as_ref().expect("marked above") {
                EGraphProofTerm::Atom(name) => name.clone(),
                EGraphProofTerm::App(function, argument) => {
                    format!("e{function} e{argument}")
                }
            };
            output.push_str(&format!("  let e{raw} := {expression}\n"));
        }
        for (index, node) in self.terms.iter().enumerate() {
            if !live_exprs[index] || matches!(node, EGraphTermNode::Raw(_)) {
                continue;
            }
            let EGraphTermNode::App(function, argument) = node else {
                unreachable!()
            };
            output.push_str(&format!(
                "  let t{index} := {} {}\n",
                self.term_name(*function),
                self.term_name(*argument)
            ));
        }
        for (index, node) in self.arena.iter().enumerate() {
            if !live[index] {
                continue;
            }
            let expression = match node.kind {
                EGraphProofKind::Refl => "rfl".to_owned(),
                EGraphProofKind::Symm(proof) => format!("Eq.symm p{}", proof.0),
                EGraphProofKind::Trans(first, second) => {
                    format!("Eq.trans p{} p{}", first.0, second.0)
                }
                EGraphProofKind::CongApp(function, argument) => {
                    format!("congr p{} p{}", function.0, argument.0)
                }
                EGraphProofKind::CongFunction { argument, proof } => {
                    format!("congrFun p{} {}", proof.0, self.term_name(argument))
                }
                EGraphProofKind::CongArgument { function, proof } => {
                    format!("congrArg {} p{}", self.term_name(function), proof.0)
                }
                EGraphProofKind::Rewrite {
                    ref name,
                    ref arguments,
                } => {
                    format!(
                        "{name}{}",
                        arguments
                            .iter()
                            .map(|raw| format!(" e{raw}"))
                            .collect::<String>()
                    )
                }
                EGraphProofKind::Assumption { index, ref label } => {
                    output.push_str(&format!("  -- {label}\n"));
                    format!("h{index}")
                }
            };
            output.push_str(&format!(
                "  let p{index} : {} = {} := {expression}\n",
                self.term_name(node.left),
                self.term_name(node.right)
            ));
        }
        output.push_str(&format!("  exact p{}\n", conclusion.0));
        Ok(output)
    }
}

impl std::error::Error for ProofError {}

/// A proof-producing union-find used as the first layer of e-graph proof generation.
///
/// Operational data stays in `parents` and `memo`. When `track_proofs` is false, no proof
/// arena or parallel proof tables are allocated. Named terms must be valid Lean expressions;
/// [`Self::lean_proof`] receives the binders that put those expressions in scope.
#[derive(Clone, Debug)]
pub struct ProofUnionFind {
    parents: Vec<Id>,
    sizes: Vec<usize>,
    memo: HashMap<String, Id>,
    names: Vec<String>,
    proofs: Option<ProofState>,
}

impl ProofUnionFind {
    pub fn new(track_proofs: bool) -> Self {
        Self {
            parents: Vec::new(),
            sizes: Vec::new(),
            memo: HashMap::default(),
            names: Vec::new(),
            proofs: track_proofs.then(ProofState::default),
        }
    }

    pub fn proofs_enabled(&self) -> bool {
        self.proofs.is_some()
    }

    pub fn make_set(&mut self, name: impl Into<String>) -> Id {
        let name = name.into();
        if let Some(&id) = self.memo.get(&name) {
            return id;
        }
        assert!(
            self.parents.len() <= Id::MAX as usize,
            "exhausted union-find IDs"
        );
        let id = self.parents.len() as Id;
        self.parents.push(id);
        self.sizes.push(1);
        self.names.push(name.clone());
        self.memo.insert(name.clone(), id);
        if let Some(proofs) = &mut self.proofs {
            let memo_proof = proofs.alloc(
                Endpoint::Named(name.clone()),
                Endpoint::Id(id),
                ProofKind::Refl,
            );
            proofs.memo_proofs.insert(name, memo_proof);
            proofs.explain_parents.push(id);
            proofs.explain_edges.push(None);
        }
        id
    }

    pub fn find(&mut self, id: Id) -> Id {
        let parent = self.parents[id as usize];
        if parent == id {
            return id;
        }
        let root = self.find(parent);
        self.parents[id as usize] = root;
        root
    }

    /// Equate two entries using an external equality assumption.
    ///
    /// The label is retained in the proof arena for diagnostics. Lean output gives assumptions
    /// stable local names (`h0`, `h1`, ...), so labels need not be valid Lean identifiers.
    pub fn union(&mut self, left: Id, right: Id, label: impl Into<String>) -> bool {
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            return false;
        }
        let left_is_smaller = self.sizes[left_root as usize] <= self.sizes[right_root as usize];
        if let Some(proofs) = &mut self.proofs {
            let assumption = proofs.assumption(left, right, label.into());
            if left_is_smaller {
                proofs.link_explanations(left, right, assumption, false);
            } else {
                proofs.link_explanations(right, left, assumption, true);
            }
        }
        let (small_root, large_root) = if left_is_smaller {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        self.parents[small_root as usize] = large_root;
        self.sizes[large_root as usize] += self.sizes[small_root as usize];
        true
    }

    pub fn equivalent(&mut self, left: Id, right: Id) -> bool {
        self.find(left) == self.find(right)
    }

    pub fn proof_step_count(&self) -> usize {
        self.proofs.as_ref().map_or(0, |proofs| proofs.arena.len())
    }

    fn proof(&mut self, left: &str, right: &str) -> Result<ProofId, ProofError> {
        let left_id = *self
            .memo
            .get(left)
            .ok_or_else(|| ProofError::UnknownName(left.to_owned()))?;
        let right_id = *self
            .memo
            .get(right)
            .ok_or_else(|| ProofError::UnknownName(right.to_owned()))?;
        if self.proofs.is_none() {
            return Err(ProofError::TrackingDisabled);
        }
        let left_root = self.find(left_id);
        let right_root = self.find(right_id);
        if left_root != right_root {
            return Err(ProofError::NotEquivalent {
                left: left.to_owned(),
                right: right.to_owned(),
            });
        }
        let proofs = self.proofs.as_mut().expect("checked above");
        let left_memo = proofs.memo_proofs[left];
        let right_memo = proofs.memo_proofs[right];
        let (left_path, right_path) = proofs.explanation_paths(left_id, right_id);
        let mut left_to_common = left_memo;
        for edge in left_path {
            let edge = proofs.oriented_edge(edge);
            left_to_common = proofs.trans(left_to_common, edge);
        }
        let mut common_to_right = None;
        for edge in right_path.into_iter().rev() {
            let edge = proofs.oriented_edge(ExplainEdge {
                reason: edge.reason,
                reversed: !edge.reversed,
            });
            common_to_right = Some(match common_to_right {
                Some(path) => proofs.trans(path, edge),
                None => edge,
            });
        }
        let right_memo = proofs.symm(right_memo);
        let common_to_right = match common_to_right {
            Some(path) => proofs.trans(path, right_memo),
            None => right_memo,
        };
        Ok(proofs.trans(left_to_common, common_to_right))
    }

    /// Print a complete Lean theorem proving the requested equality.
    ///
    /// `binders` is inserted after the theorem name, for example
    /// `"{α : Type} (a b c : α)"`.
    pub fn lean_proof(
        &mut self,
        theorem_name: &str,
        binders: &str,
        left: &str,
        right: &str,
    ) -> Result<String, ProofError> {
        let conclusion = self.proof(left, right)?;
        let proofs = self.proofs.as_ref().expect("proof() checked tracking");
        let live = proofs.live_from(conclusion);
        let mut output = format!("theorem {theorem_name} {binders}");
        for (is_live, node) in live.iter().zip(&proofs.arena) {
            if !is_live {
                continue;
            }
            if let ProofKind::Assumption { index, .. } = node.kind {
                output.push_str(&format!(
                    " (h{index} : {} = {})",
                    self.endpoint_source(&node.left),
                    self.endpoint_source(&node.right)
                ));
            }
        }
        output.push_str(&format!(" : {left} = {right} := by\n"));
        let mut live_terms = vec![false; self.names.len()];
        for (is_live, node) in live.iter().zip(&proofs.arena) {
            if *is_live {
                for endpoint in [&node.left, &node.right] {
                    if let Endpoint::Id(id) = endpoint {
                        live_terms[*id as usize] = true;
                    }
                }
            }
        }
        for (id, (is_live, name)) in live_terms.iter().zip(&self.names).enumerate() {
            if *is_live {
                output.push_str(&format!("  let e{id} := {name}\n"));
            }
        }
        for (index, node) in proofs.arena.iter().enumerate() {
            if !live[index] {
                continue;
            }
            let expression = match node.kind {
                ProofKind::Refl => "rfl".to_owned(),
                ProofKind::Symm(proof) => format!("Eq.symm p{}", proof.0),
                ProofKind::Trans(first, second) => {
                    format!("Eq.trans p{} p{}", first.0, second.0)
                }
                ProofKind::Assumption { index, ref label } => {
                    output.push_str(&format!("  -- {label}\n"));
                    format!("h{index}")
                }
            };
            output.push_str(&format!(
                "  let p{index} : {} = {} := {expression}\n",
                self.endpoint_local(&node.left),
                self.endpoint_local(&node.right)
            ));
        }
        output.push_str(&format!("  exact p{}\n", conclusion.0));
        Ok(output)
    }

    fn endpoint_local(&self, endpoint: &Endpoint) -> String {
        match endpoint {
            Endpoint::Named(name) => name.clone(),
            Endpoint::Id(id) => format!("e{id}"),
        }
    }

    fn endpoint_source(&self, endpoint: &Endpoint) -> String {
        match endpoint {
            Endpoint::Named(name) => name.clone(),
            Endpoint::Id(id) => self.names[*id as usize].clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    #[test]
    fn proof_tracking_has_no_arena_when_disabled() {
        let mut union_find = ProofUnionFind::new(false);
        let a = union_find.make_set("a");
        let b = union_find.make_set("b");
        union_find.union(a, b, "a equals b");
        assert!(union_find.equivalent(a, b));
        assert_eq!(union_find.proof_step_count(), 0);
        assert_eq!(
            union_find.lean_proof("disabled", "(a b : Int)", "a", "b"),
            Err(ProofError::TrackingDisabled)
        );
    }

    #[test]
    fn prints_an_explanation_path_transitivity_proof() {
        let mut union_find = ProofUnionFind::new(true);
        let a = union_find.make_set("a");
        let b = union_find.make_set("b");
        let c = union_find.make_set("c");
        union_find.union(a, b, "a-to-b");
        union_find.union(b, c, "b-to-c");
        let lean = union_find
            .lean_proof("uf_chain", "{α : Type} (a b c : α)", "a", "c")
            .unwrap();
        assert!(lean.contains("(h0 : a = b)"));
        assert!(lean.contains("(h1 : b = c)"));
        assert!(lean.contains("Eq.trans"));
        assert!(!lean.contains("e0 = e0"));
        assert!(lean.ends_with('\n'));
    }

    #[test]
    fn explanation_forest_omits_unions_beyond_the_requested_path() {
        let mut union_find = ProofUnionFind::new(true);
        let a = union_find.make_set("a");
        let b = union_find.make_set("b");
        let c = union_find.make_set("c");
        let d = union_find.make_set("d");
        union_find.union(a, b, "needed a-to-b");
        union_find.union(c, d, "irrelevant c-to-d");
        union_find.union(b, c, "irrelevant bridge");

        let lean = union_find
            .lean_proof("uf_direct", "{α : Type} (a b c d : α)", "a", "b")
            .unwrap();
        assert!(lean.contains("(h0 : a = b)"));
        assert!(lean.contains("needed a-to-b"));
        assert!(!lean.contains("irrelevant c-to-d"));
        assert!(!lean.contains("irrelevant bridge"));
        assert!(!lean.contains("(h1"));
        assert!(!lean.contains("(h2"));
    }

    #[test]
    fn printing_eliminates_disconnected_proofs_and_terms() {
        let mut union_find = ProofUnionFind::new(true);
        let a = union_find.make_set("a");
        let b = union_find.make_set("b");
        let c = union_find.make_set("c");
        let _d = union_find.make_set("d");
        let e = union_find.make_set("e");
        let f = union_find.make_set("f");
        union_find.union(a, b, "a-to-b");
        union_find.union(b, c, "b-to-c");
        union_find.union(e, f, "disconnected e-to-f");
        let lean = union_find
            .lean_proof("uf_larger", "{α : Type} (a b c d e f : α)", "a", "c")
            .unwrap();
        assert!(!lean.contains("let e3"));
        assert!(!lean.contains("let e4"));
        assert!(!lean.contains("let e5"));
        assert!(!lean.contains("disconnected e-to-f"));
        assert!(!lean.contains("(h2"));
    }

    #[test]
    fn generated_certificate_is_accepted_by_lean_when_available() {
        let Ok(mut lean) = Command::new("lean")
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
        else {
            return;
        };
        let mut union_find = ProofUnionFind::new(true);
        let a = union_find.make_set("a");
        let b = union_find.make_set("b");
        let c = union_find.make_set("c");
        let _d = union_find.make_set("d");
        let e = union_find.make_set("e");
        let f = union_find.make_set("f");
        union_find.union(a, b, "a-to-b");
        union_find.union(b, c, "b-to-c");
        union_find.union(e, f, "disconnected e-to-f");
        let certificate = union_find
            .lean_proof("uf_larger", "{α : Type} (a b c d e f : α)", "a", "c")
            .unwrap();
        lean.stdin
            .take()
            .unwrap()
            .write_all(certificate.as_bytes())
            .unwrap();
        let output = lean.wait_with_output().unwrap();
        assert!(
            output.status.success(),
            "Lean rejected the generated certificate:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
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
        let delayed = egraph.proof_stats().unwrap();
        assert_eq!(delayed.congruence, 0);
        assert_eq!(delayed.explanation_reasons, 3);

        let certificate = egraph
            .lean_proof(
                "first_order_congruence",
                "{α : Type} (f : α → α) (a b : α)",
                &fa,
                &fb,
            )
            .unwrap();
        assert!(certificate.contains("congrArg e0"));
        assert!(egraph.proof_stats().unwrap().congruence > 0);
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
        assert_eq!(egraph.proof_stats().unwrap().rewrites, 0);
        let settled_steps = egraph.proof_step_count();
        egraph.saturate(std::slice::from_ref(&rule));
        assert_eq!(egraph.proof_step_count(), settled_steps);

        let certificate = egraph
            .lean_proof(
                "two_rewrites",
                "{α : Type} (plus : α → α → α) (zero x : α) \
                 (r1 : ∀ a, plus a zero = a)",
                &outer,
                &x,
            )
            .unwrap();
        assert_eq!(egraph.proof_stats().unwrap().rewrites, 2);
        assert_eq!(certificate.matches("r1 e").count(), 2);
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
