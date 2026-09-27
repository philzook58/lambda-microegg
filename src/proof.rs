use crate::{Pattern, RawId, Rewrite, Subst};
use rustc_hash::FxHashMap as HashMap;

/// The original syntax allocated at a raw e-class ID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EGraphTermDefinition {
    Atom(String),
    App(RawId, RawId),
}

/// Index of one equality reason retained by the explanation forest.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ReasonId(u32);

/// One instantiated pattern node and its current representative.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct PatternNodeWitness {
    pub(crate) raw: RawId,
    pub(crate) normal: RawId,
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

/// An equality reason together with the two raw IDs it connects.
#[derive(Clone, Debug)]
struct ReasonNode {
    left: RawId,
    right: RawId,
    reason: Reason,
}

/// One parent link in the uncompressed explanation forest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExplainEdge {
    reason: ReasonId,
    reversed: bool,
}

/// Why the endpoints of one explanation-forest edge are equal.
#[derive(Clone, Debug)]
pub(crate) enum Reason {
    /// The two raw IDs unfold to the same atom or application.
    Definitional,
    /// An equality supplied directly by the caller.
    Assumption { index: usize, label: String },
    /// One successful application of a named rewrite rule.
    Rewrite {
        rule: RuleId,
        subst: Subst,
        normalization: Option<RewriteNormalization>,
    },
    /// Two applications whose function and argument classes were already equal.
    Congruence {
        left_function: RawId,
        right_function: RawId,
        left_argument: RawId,
        right_argument: RawId,
    },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EGraphProofTrace {
    // Source terms, indexed by RawId.
    definitions: Vec<Option<EGraphTermDefinition>>,
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
        self.explain_parents.push(raw);
        self.explain_edges.push(None);
        self.explain_sizes.push(1);
        if context != 0 {
            self.unsupported(format!("e{raw} was allocated in context {context}"));
        }
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

    fn explanation_path(&self, left: RawId, right: RawId) -> ExplanationPath {
        if left == right {
            return ExplanationPath {
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
            .map(|edge| ReasonUse {
                reason: edge.reason,
                reversed: edge.reversed,
            })
            .collect::<Vec<_>>();
        reasons.extend(right_edges.into_iter().rev().map(|edge| ReasonUse {
            reason: edge.reason,
            reversed: !edge.reversed,
        }));
        ExplanationPath {
            left,
            right,
            reasons,
        }
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

    pub(crate) fn link_explanation(&mut self, left: RawId, right: RawId, reason: Reason) {
        let left_root = self.explanation_root(left);
        let right_root = self.explanation_root(right);
        assert_ne!(
            left_root, right_root,
            "a proof edge must join two components"
        );
        let reason = self.alloc_reason(ReasonNode {
            left,
            right,
            reason,
        });

        if self.explain_sizes[left_root as usize] <= self.explain_sizes[right_root as usize] {
            self.reroot_explanation(left);
            let right_root = self.explanation_root(right);
            let left_size = self.explain_sizes[left as usize];
            self.explain_parents[left as usize] = right;
            self.explain_edges[left as usize] = Some(ExplainEdge {
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
            self.explain_edges[right as usize] = Some(ExplainEdge {
                reason,
                reversed: true,
            });
            self.explain_sizes[right as usize] = 0;
            self.explain_sizes[left_root as usize] += right_size;
        }
    }

    pub(crate) fn stats(&self) -> EGraphProofStats {
        EGraphProofStats {
            explanation_edges: self.explain_edges.iter().flatten().count(),
            explanation_reasons: self.reasons.len(),
        }
    }
}

// Lean certificate construction. Everything below is ephemeral for one print request.
/// One stored reason, oriented as it is used in the requested equality path.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ReasonUse {
    reason: ReasonId,
    reversed: bool,
}

/// The unique explanation-forest path selected for the requested equality.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct ExplanationPath {
    left: RawId,
    right: RawId,
    reasons: Vec<ReasonUse>,
}

/// An index into the proof-expression arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofId(pub(crate) u32);

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
struct EGraphTermId(u32);

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum EGraphTermNode {
    Raw(RawId),
    App(EGraphTermId, EGraphTermId),
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
    left: RawId,
    right: RawId,
) -> Result<String, ProofError> {
    let mut arena = EGraphProofArena::default();
    let conclusion = arena.proof_between(trace, left, right);
    arena.render(trace, theorem_name, binders, left, right, conclusion)
}

impl EGraphProofTrace {
    fn source_term(&self, raw: RawId) -> Result<String, ProofError> {
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphTermDefinition::Atom(name)) => Ok(name.clone()),
            Some(EGraphTermDefinition::App(function, argument)) => {
                let function = self.source_term(*function)?;
                let argument_text = self.source_term(*argument)?;
                let argument = match self.definitions[*argument as usize].as_ref() {
                    Some(EGraphTermDefinition::App(_, _)) => format!("({argument_text})"),
                    _ => argument_text,
                };
                Ok(format!("{function} {argument}"))
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn mark_term(&self, raw: RawId, live: &mut [bool]) -> Result<(), ProofError> {
        if std::mem::replace(&mut live[raw as usize], true) {
            return Ok(());
        }
        match self.definitions[raw as usize].as_ref() {
            Some(EGraphTermDefinition::Atom(_)) => Ok(()),
            Some(EGraphTermDefinition::App(function, argument)) => {
                self.mark_term(*function, live)?;
                self.mark_term(*argument, live)
            }
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }
}

impl EGraphProofArena {
    fn alloc(&mut self, left: EGraphTermId, right: EGraphTermId, kind: EGraphProofKind) -> ProofId {
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

    fn app_term(&mut self, function: EGraphTermId, argument: EGraphTermId) -> EGraphTermId {
        self.alloc_term(EGraphTermNode::App(function, argument))
    }

    fn refl_between(&mut self, left: RawId, right: RawId) -> ProofId {
        let left = self.raw_term(left);
        let right = self.raw_term(right);
        self.refl_terms(left, right)
    }

    fn refl_terms(&mut self, left: EGraphTermId, right: EGraphTermId) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Refl)
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

    fn congr_app(
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
        left: EGraphTermId,
        right: EGraphTermId,
        name: String,
        arguments: Vec<RawId>,
    ) -> ProofId {
        self.alloc(left, right, EGraphProofKind::Rewrite { name, arguments })
    }

    fn raw_app_to(
        &mut self,
        trace: &EGraphProofTrace,
        raw: RawId,
        function: RawId,
        argument: RawId,
    ) -> Option<ProofId> {
        let EGraphTermDefinition::App(old_function, old_argument) = trace.definition(raw)? else {
            return None;
        };
        let fp = self.proof_between(trace, old_function, function);
        let ap = self.proof_between(trace, old_argument, argument);
        let old_function = self.raw_term(old_function);
        let old_argument = self.raw_term(old_argument);
        let definition = self.app_term(old_function, old_argument);
        let raw = self.raw_term(raw);
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
                let left = self.raw_term(node.left);
                let right = self.raw_term(node.right);
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
                        subst
                            .get(name)
                            .expect("complete rewrite substitution")
                            .raw()
                    })
                    .collect();
                if normalization.is_none() {
                    let left = self.raw_term(node.left);
                    let right = self.raw_term(node.right);
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
        };
        self.materialized_reasons[reason.0 as usize] = Some(proof);
        proof
    }

    fn materialize_pattern(
        &mut self,
        trace: &EGraphProofTrace,
        pattern: &Pattern,
        witnesses: &[PatternNodeWitness],
    ) -> (EGraphTermId, ProofId) {
        fn go(
            arena: &mut EGraphProofArena,
            trace: &EGraphProofTrace,
            pattern: &Pattern,
            witnesses: &mut std::slice::Iter<'_, PatternNodeWitness>,
        ) -> (EGraphTermId, ProofId, RawId) {
            match pattern {
                Pattern::MetaVar(_, _) | Pattern::Atom(_) => {
                    let witness = witnesses.next().expect("pattern leaf witness");
                    let term = arena.raw_term(witness.raw);
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

    fn materialize_path(&mut self, trace: &EGraphProofTrace, path: ExplanationPath) -> ProofId {
        let mut proof = None;
        for reason_use in path.reasons {
            let mut step = self.materialize_reason(trace, reason_use.reason);
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

    fn proof_between(&mut self, trace: &EGraphProofTrace, left: RawId, right: RawId) -> ProofId {
        if self.materialized_reasons.len() < trace.reasons.len() {
            self.materialized_reasons.resize(trace.reasons.len(), None);
        }
        let path = trace.explanation_path(left, right);
        self.materialize_path(trace, path)
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
        trace: &EGraphProofTrace,
        term: EGraphTermId,
        live_terms: &mut [bool],
        live_exprs: &mut [bool],
    ) -> Result<(), ProofError> {
        if std::mem::replace(&mut live_exprs[term.0 as usize], true) {
            return Ok(());
        }
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => trace.mark_term(raw, live_terms),
            EGraphTermNode::App(function, argument) => {
                self.mark_endpoint(trace, function, live_terms, live_exprs)?;
                self.mark_endpoint(trace, argument, live_terms, live_exprs)
            }
        }
    }

    fn render(
        &self,
        trace: &EGraphProofTrace,
        theorem_name: &str,
        binders: &str,
        left: RawId,
        right: RawId,
        conclusion: ProofId,
    ) -> Result<String, ProofError> {
        if let Some(message) = &trace.unsupported {
            return Err(ProofError::Unsupported(message.clone()));
        }
        let live = self.live_from(conclusion);
        let mut output = format!("theorem {theorem_name} {binders}");
        for (is_live, node) in live.iter().zip(&self.proofs) {
            if *is_live && let EGraphProofKind::Assumption { index, .. } = node.kind {
                let left = self.raw_endpoint(node.left)?;
                let right = self.raw_endpoint(node.right)?;
                output.push_str(&format!(
                    " (h{index} : {} = {})",
                    trace.source_term(left)?,
                    trace.source_term(right)?
                ));
            }
        }
        output.push_str(&format!(
            " : {} = {} := by\n",
            trace.source_term(left)?,
            trace.source_term(right)?
        ));

        let mut live_terms = vec![false; trace.definitions.len()];
        let mut live_exprs = vec![false; self.terms.len()];
        trace.mark_term(left, &mut live_terms)?;
        trace.mark_term(right, &mut live_terms)?;
        for (is_live, node) in live.iter().zip(&self.proofs) {
            if *is_live {
                self.mark_endpoint(trace, node.left, &mut live_terms, &mut live_exprs)?;
                self.mark_endpoint(trace, node.right, &mut live_terms, &mut live_exprs)?;
                if let EGraphProofKind::Rewrite { ref arguments, .. } = node.kind {
                    for &raw in arguments {
                        trace.mark_term(raw, &mut live_terms)?;
                    }
                }
            }
        }
        for (raw, is_live) in live_terms.into_iter().enumerate() {
            if !is_live {
                continue;
            }
            let expression = match trace.definitions[raw].as_ref().expect("marked above") {
                EGraphTermDefinition::Atom(name) => name.clone(),
                EGraphTermDefinition::App(function, argument) => {
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
        for (index, node) in self.proofs.iter().enumerate() {
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
        assert!(certificate.contains("congrArg e0"));
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
