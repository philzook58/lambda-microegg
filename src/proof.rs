use rustc_hash::FxHashMap as HashMap;

use crate::RawId;

/// An index into the proof-expression arena.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProofId(u32);

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

#[derive(Clone, Debug, Default)]
struct ProofState {
    arena: Vec<ProofNode>,
    /// Proof that each union-find entry equals its current parent entry.
    parent_proofs: Vec<ProofId>,
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

    fn refl(&mut self, endpoint: Endpoint) -> ProofId {
        self.alloc(endpoint.clone(), endpoint, ProofKind::Refl)
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
        normalizers: Vec<ProofId>,
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
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EGraphProofState {
    arena: Vec<EGraphProofNode>,
    proof_memo: HashMap<EGraphProofNode, ProofId>,
    terms: Vec<EGraphTermNode>,
    term_memo: HashMap<EGraphTermNode, EGraphTermId>,
    raw_terms: Vec<EGraphTermId>,
    definitions: Vec<Option<EGraphProofTerm>>,
    parent_proofs: Vec<ProofId>,
    assumptions: usize,
    unsupported: Option<String>,
}

impl EGraphProofState {
    pub(crate) fn step_count(&self) -> usize {
        self.arena.len()
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
        let proof = self.alloc(term, term, EGraphProofKind::Refl);
        self.parent_proofs.push(proof);
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

    pub(crate) fn parent_proof(&self, raw: RawId) -> ProofId {
        self.parent_proofs[raw as usize]
    }

    pub(crate) fn set_parent_proof(&mut self, child: RawId, proof: ProofId) {
        debug_assert_eq!(self.arena[proof.0 as usize].left, self.raw_term(child));
        self.parent_proofs[child as usize] = proof;
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

    pub(crate) fn rewrite_normalized(
        &mut self,
        left: RawId,
        right: RawId,
        name: String,
        arguments: Vec<RawId>,
        normalizers: Vec<ProofId>,
    ) -> ProofId {
        self.alloc(
            self.raw_term(left),
            self.raw_term(right),
            EGraphProofKind::Rewrite {
                name,
                arguments,
                normalizers,
            },
        )
    }

    pub(crate) fn proof_between(&mut self, left: RawId, right: RawId) -> ProofId {
        let left = self.parent_proof(left);
        let right = self.parent_proof(right);
        let right = self.symm(right);
        self.trans(left, right)
    }

    pub(crate) fn is_refl(&self, proof: ProofId) -> bool {
        let node = &self.arena[proof.0 as usize];
        node.left == node.right && matches!(node.kind, EGraphProofKind::Refl)
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
                EGraphProofKind::Rewrite {
                    ref normalizers, ..
                } => work.extend(normalizers),
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
            Some(EGraphProofTerm::App(function, argument)) => Ok(format!(
                "app ({}) ({})",
                self.source_term(*function)?,
                self.source_term(*argument)?
            )),
            None => Err(ProofError::Unsupported(format!(
                "e{raw} has no first-order definition"
            ))),
        }
    }

    fn raw_endpoint(&self, term: EGraphTermId) -> Result<RawId, ProofError> {
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => Ok(raw),
        }
    }

    fn term_name(&self, term: EGraphTermId) -> String {
        match self.terms[term.0 as usize] {
            EGraphTermNode::Raw(raw) => format!("e{raw}"),
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
                    format!("app e{function} e{argument}")
                }
            };
            output.push_str(&format!("  let e{raw} := {expression}\n"));
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
                    format!("congr (congrArg app p{}) p{}", function.0, argument.0)
                }
                EGraphProofKind::CongFunction { argument, proof } => {
                    format!(
                        "congrFun (congrArg app p{}) {}",
                        proof.0,
                        self.term_name(argument)
                    )
                }
                EGraphProofKind::CongArgument { function, proof } => {
                    format!("congrArg (app {}) p{}", self.term_name(function), proof.0)
                }
                EGraphProofKind::Rewrite {
                    ref name,
                    ref arguments,
                    ref normalizers,
                } => {
                    let rules = normalizers
                        .iter()
                        .map(|proof| format!("p{}", proof.0))
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!(
                        "by simpa only [{rules}] using {name}{}",
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
    memo: HashMap<String, Id>,
    names: Vec<String>,
    proofs: Option<ProofState>,
}

impl ProofUnionFind {
    pub fn new(track_proofs: bool) -> Self {
        Self {
            parents: Vec::new(),
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
        self.names.push(name.clone());
        self.memo.insert(name.clone(), id);
        if let Some(proofs) = &mut self.proofs {
            let memo_proof = proofs.alloc(
                Endpoint::Named(name.clone()),
                Endpoint::Id(id),
                ProofKind::Refl,
            );
            let parent_proof = proofs.refl(Endpoint::Id(id));
            proofs.memo_proofs.insert(name, memo_proof);
            proofs.parent_proofs.push(parent_proof);
        }
        id
    }

    pub fn find(&mut self, id: Id) -> Id {
        let parent = self.parents[id as usize];
        if parent == id {
            return id;
        }
        let root = self.find(parent);
        if let Some(proofs) = &mut self.proofs {
            let edge = proofs.parent_proofs[id as usize];
            let suffix = proofs.parent_proofs[parent as usize];
            proofs.parent_proofs[id as usize] = proofs.trans(edge, suffix);
        }
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
        if let Some(proofs) = &mut self.proofs {
            let left_path = proofs.parent_proofs[left as usize];
            let right_path = proofs.parent_proofs[right as usize];
            let assumption = proofs.assumption(left, right, label.into());
            let left_path = proofs.symm(left_path);
            let root_to_right = proofs.trans(left_path, assumption);
            let root_to_root = proofs.trans(root_to_right, right_path);
            proofs.parent_proofs[left_root as usize] = root_to_root;
        }
        self.parents[left_root as usize] = right_root;
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
        let left_path = proofs.parent_proofs[left_id as usize];
        let right_memo = proofs.memo_proofs[right];
        let right_path = proofs.parent_proofs[right_id as usize];
        let left_to_root = proofs.trans(left_memo, left_path);
        let right_to_root = proofs.trans(right_memo, right_path);
        let root_to_right = proofs.symm(right_to_root);
        Ok(proofs.trans(left_to_root, root_to_right))
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
    fn prints_a_path_compressed_transitivity_proof() {
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

        let certificate = egraph
            .lean_proof(
                "first_order_congruence",
                "{α : Type} (app : α → α → α) (f a b : α)",
                &fa,
                &fb,
            )
            .unwrap();
        assert!(certificate.contains("congrArg (app e0)"));
        assert!(!certificate.contains("irrelevant equality"));
        assert!(!certificate.contains("let e5"));
        assert!(!certificate.contains("let p0"));

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
                "{α : Type} (app : α → α → α) (f g a b : α)",
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
                "{α : Type} (app : α → α → α) (f g a : α)",
                &fa,
                &ga,
            )
            .unwrap();
        assert!(certificate.contains("congrFun (congrArg app"));

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
        let settled_steps = egraph.proof_step_count();
        egraph.saturate(std::slice::from_ref(&rule));
        assert_eq!(egraph.proof_step_count(), settled_steps);

        let certificate = egraph
            .lean_proof(
                "two_rewrites",
                "{α : Type} (app : α → α → α) (plus zero x : α) \
                 (r1 : ∀ a, app (app plus a) zero = a)",
                &outer,
                &x,
            )
            .unwrap();
        assert_eq!(certificate.matches("using r1").count(), 1);

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
