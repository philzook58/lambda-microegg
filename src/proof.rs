use rustc_hash::FxHashMap as HashMap;

/// An index into the proof-expression arena.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
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
}

impl std::fmt::Display for ProofError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TrackingDisabled => write!(formatter, "proof tracking is disabled"),
            Self::UnknownName(name) => write!(formatter, "unknown term {name:?}"),
            Self::NotEquivalent { left, right } => {
                write!(formatter, "{left:?} and {right:?} are not equivalent")
            }
        }
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
}
