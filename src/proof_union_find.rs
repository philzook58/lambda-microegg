//! Standalone proof-producing union-find experiment.
//!
//! Lambda Micro Egg's `EGraph` does not use this implementation. It is kept for the
//! Oliveras-style explanation-forest tests, examples, and measurements that guided
//! the e-graph proof recorder. Production e-graph proof generation lives in `proof.rs`.
//!
//! The thinning experiment is deliberately single-sorted. An entry of arity `n`
//! denotes a curried Lean function `α → ... → α` with `n` inputs; an ordinary
//! constant has arity zero. Constructing a restricted witness fills every removed
//! input with `default`, so generated theorems that prune dependencies require
//! `[Inhabited α]`. This construction is not stored in explanation-forest edges.

use rustc_hash::FxHashMap as HashMap;

use crate::proof::{ProofError, ProofId};
use crate::{Id, Lift, RawId};

/// A partially known lift used only while reconciling two explanation paths.
///
/// The two lifts share a domain. Their selected positions are connected, while
/// unselected source positions have not been chosen yet. A completed path always
/// has an identity `source`, leaving one ordinary `target` lift.
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

    fn total(thinning: Lift) -> Self {
        Self::new(Lift::identity(thinning.dom()), thinning)
    }

    fn reverse(&self) -> Self {
        Self::new(self.target, self.source)
    }

    /// Apply `outer` after this partial wiring.
    fn then(&self, outer: &Self) -> Self {
        assert_eq!(self.target.cod(), outer.source.cod());
        let pullback = self.target.pullback(&outer.source);
        Self::new(
            self.source.compose(&pullback.from_left),
            outer.target.compose(&pullback.from_right),
        )
    }

    /// Combine compatible partial wirings between the same two contexts.
    fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.source.cod(), other.source.cod());
        assert_eq!(self.target.cod(), other.target.cod());
        let source = self.source.union(&other.source).lift;
        let target = self.target.union(&other.target).lift;
        let merged = Self::new(source, target);
        for map in [self, other] {
            let source_positions = source.factor(&map.source).unwrap();
            let target_positions = target.factor(&map.target).unwrap();
            assert_eq!(
                source_positions, target_positions,
                "incompatible partial thinnings"
            );
        }
        merged
    }

    fn finish(&self) -> Lift {
        assert!(
            self.source.is_identity(),
            "an explanation path did not determine a total lift"
        );
        self.target
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Endpoint {
    Named { name: String, lift: Lift },
    Raw { raw: RawId, lift: Lift },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ProofKind {
    Refl,
    Symm(ProofId),
    Trans(ProofId, ProofId),
    Lift {
        proof: ProofId,
        lift: Lift,
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ProofNode {
    /// A node proves pointwise equality of these contextual terms. It proves
    /// ordinary equality when their ambient context has arity zero.
    left: Endpoint,
    right: Endpoint,
    kind: ProofKind,
}

/// A canonical edge proves `larger = lift(thinning, smaller)`.
/// `reversed` records which endpoint is the forest child after rerooting.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExplainEdge {
    forward: ProofId,
    thinning: Lift,
    reversed: bool,
}

#[derive(Clone, Debug, Default)]
struct ProofState {
    arena: Vec<ProofNode>,
    /// The separate, uncompressed forest can be rerooted independently of operational UF.
    explain_parents: Vec<RawId>,
    explain_edges: Vec<Option<ExplainEdge>>,
    /// Proof that each named term equals the e-class allocated for it.
    memo_proofs: HashMap<String, ProofId>,
    assumptions: usize,
}

#[derive(Clone, Debug)]
enum Definition {
    Named(String),
    /// Restrict `source` to the variables selected by `thinning`, filling the rest with `default`.
    Restrict {
        source: RawId,
        thinning: Lift,
    },
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
            Endpoint::Raw {
                raw: left.raw(),
                lift: left.lift(),
            },
            Endpoint::Raw {
                raw: right.raw(),
                lift: right.lift(),
            },
            ProofKind::Assumption { index, label },
        )
    }

    fn lift_endpoint(endpoint: &Endpoint, outer: Lift) -> Endpoint {
        match endpoint {
            Endpoint::Named { name, lift } => Endpoint::Named {
                name: name.clone(),
                lift: outer.compose(lift),
            },
            Endpoint::Raw { raw, lift } => Endpoint::Raw {
                raw: *raw,
                lift: outer.compose(lift),
            },
        }
    }

    fn lift_proof(&mut self, proof: ProofId, lift: Lift) -> ProofId {
        if lift.is_identity() {
            return proof;
        }
        let node = &self.arena[proof.0 as usize];
        let left = Self::lift_endpoint(&node.left, lift);
        let right = Self::lift_endpoint(&node.right, lift);
        self.alloc(left, right, ProofKind::Lift { proof, lift })
    }

    fn reroot_explanation(&mut self, node: RawId) {
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
                reversed: !current_edge.reversed,
                ..current_edge
            });
            current = parent;
            parent = next_parent;
            edge = next_edge;
        }
    }

    /// Record `larger = lift(thinning, smaller)`. Rerooting changes only the
    /// forest orientation flag; the stored relation remains this ordinary lift.
    fn link_thinning_equality(
        &mut self,
        larger: RawId,
        smaller: RawId,
        proof: ProofId,
        thinning: Lift,
    ) {
        self.reroot_explanation(smaller);
        debug_assert_eq!(self.explain_parents[smaller as usize], smaller);
        debug_assert!(self.explain_edges[smaller as usize].is_none());
        self.explain_parents[smaller as usize] = larger;
        self.explain_edges[smaller as usize] = Some(ExplainEdge {
            forward: proof,
            thinning,
            reversed: true,
        });
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

    fn explain(&mut self, left: Id, right: Id) -> ProofId {
        let (left_path, right_path) = self.explanation_paths(left.raw(), right.raw());
        let mut left_maps = Self::plan_path(left, &left_path);
        let mut right_maps = Self::plan_path(right, &right_path);
        Self::complete_paths(&mut left_maps, &left_path, &mut right_maps, &right_path);
        debug_assert!(
            left_maps
                .iter()
                .chain(&right_maps)
                .all(|map| map.source.is_identity()),
            "a completed explanation path must contain only ordinary lifts"
        );

        let left_to_common = self.materialize_path(left, &left_path, &left_maps);
        let right_to_common = self.materialize_path(right, &right_path, &right_maps);
        let common_to_right = self.symm(right_to_common);
        let proof = self.trans(left_to_common, common_to_right);
        debug_assert_eq!(
            self.arena[proof.0 as usize].right,
            Endpoint::Raw {
                raw: right.raw(),
                lift: right.lift(),
            },
            "explanation forest disagrees with operational thinning"
        );
        proof
    }

    fn complete_paths(
        left: &mut [PartialLift],
        left_edges: &[ExplainEdge],
        right: &mut [PartialLift],
        right_edges: &[ExplainEdge],
    ) {
        let common = left.last().unwrap().merge(right.last().unwrap());
        *left.last_mut().unwrap() = common;
        *right.last_mut().unwrap() = common;
        Self::complete_path(left, left_edges);
        Self::complete_path(right, right_edges);
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

    fn materialize_path(
        &mut self,
        start: Id,
        path: &[ExplainEdge],
        maps: &[PartialLift],
    ) -> ProofId {
        let endpoint = Endpoint::Raw {
            raw: start.raw(),
            lift: maps[0].finish(),
        };
        let mut proof = self.alloc(endpoint.clone(), endpoint, ProofKind::Refl);
        for (index, &edge) in path.iter().enumerate() {
            let mapped = if edge.reversed {
                let mapped = self.lift_proof(edge.forward, maps[index + 1].finish());
                self.symm(mapped)
            } else {
                self.lift_proof(edge.forward, maps[index].finish())
            };
            proof = self.trans(proof, mapped);
        }
        proof
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
                ProofKind::Symm(child) | ProofKind::Lift { proof: child, .. } => work.push(child),
                ProofKind::SpecializeLeft { equality, .. }
                | ProofKind::SpecializeRight { equality, .. }
                | ProofKind::FactorLeft { equality, .. }
                | ProofKind::FactorRight { equality, .. } => work.push(equality),
                ProofKind::Trans(left, right) => {
                    work.push(left);
                    work.push(right);
                }
            }
        }
        live
    }
}

/// A proof-producing union-find used as the first layer of e-graph proof generation.
///
/// Operational data stays in `parents` and `memo`. When `track_proofs` is false, no proof
/// arena or parallel proof tables are allocated. Named terms must be valid Lean expressions;
/// [`Self::lean_proof`] receives the binders that put those expressions in scope.
#[derive(Clone, Debug)]
pub struct ProofUnionFind {
    parents: Vec<Id>,
    memo: HashMap<String, RawId>,
    definitions: Vec<Definition>,
    arities: Vec<usize>,
    proofs: Option<ProofState>,
}

impl ProofUnionFind {
    pub fn new(track_proofs: bool) -> Self {
        Self {
            parents: Vec::new(),
            memo: HashMap::default(),
            definitions: Vec::new(),
            arities: Vec::new(),
            proofs: track_proofs.then(ProofState::default),
        }
    }

    pub fn proofs_enabled(&self) -> bool {
        self.proofs.is_some()
    }

    pub fn make_set(&mut self, name: impl Into<String>) -> Id {
        self.make_set_with_arity(name, 0)
    }

    /// Add a term taking `arity` arguments from the single Lean carrier type.
    pub fn make_set_with_arity(&mut self, name: impl Into<String>, arity: usize) -> Id {
        let name = name.into();
        if let Some(&raw) = self.memo.get(&name) {
            assert_eq!(self.arities[raw as usize], arity, "term arity changed");
            return Id::new(Lift::identity(arity), raw);
        }
        assert!(
            self.parents.len() <= RawId::MAX as usize,
            "exhausted union-find IDs"
        );
        let raw = self.parents.len() as RawId;
        let id = Id::new(Lift::identity(arity), raw);
        self.parents.push(id);
        self.definitions.push(Definition::Named(name.clone()));
        self.arities.push(arity);
        self.memo.insert(name.clone(), raw);
        if let Some(proofs) = &mut self.proofs {
            let memo_proof = proofs.alloc(
                Endpoint::Named {
                    name: name.clone(),
                    lift: Lift::identity(arity),
                },
                Endpoint::Raw {
                    raw,
                    lift: Lift::identity(arity),
                },
                ProofKind::Refl,
            );
            proofs.memo_proofs.insert(name, memo_proof);
            proofs.explain_parents.push(raw);
            proofs.explain_edges.push(None);
        }
        id
    }

    /// Place a raw term in a larger context at the selected argument positions.
    pub fn place(&self, id: Id, ambient_arity: usize, positions: &[usize]) -> Id {
        assert_eq!(positions.len(), self.arities[id.raw() as usize]);
        assert!(positions.iter().all(|&position| position < ambient_arity));
        assert!(positions.windows(2).all(|pair| pair[0] < pair[1]));
        Id::new(Lift::selected(ambient_arity, positions), id.raw())
    }

    pub fn find(&mut self, id: Id) -> Id {
        let parent = self.parents[id.raw() as usize];
        if parent.raw() == id.raw() {
            return id;
        }
        let root = self.find(parent);
        self.parents[id.raw() as usize] = root;
        Id::new(id.lift().compose(&root.lift()), root.raw())
    }

    fn make_restriction(&mut self, source: RawId, thinning: Lift) -> Id {
        let raw = self.parents.len() as RawId;
        let arity = thinning.dom();
        let id = Id::new(Lift::identity(arity), raw);
        self.parents.push(id);
        self.definitions
            .push(Definition::Restrict { source, thinning });
        self.arities.push(arity);
        if let Some(proofs) = &mut self.proofs {
            proofs.explain_parents.push(raw);
            proofs.explain_edges.push(None);
        }
        id
    }

    /// Equate two entries using an external equality assumption.
    ///
    /// The label is retained in the proof arena for diagnostics. Lean output gives assumptions
    /// stable local names (`h0`, `h1`, ...), so labels need not be valid Lean identifiers.
    pub fn union(&mut self, left: Id, right: Id, label: impl Into<String>) -> bool {
        assert_eq!(left.ctx(), right.ctx(), "equality needs a shared context");
        let left_root = self.find(left);
        let right_root = self.find(right);
        if left_root == right_root {
            return false;
        }
        let pullback = left_root.lift().pullback(&right_root.lift());
        let root_equality = if let Some(proofs) = &mut self.proofs {
            let assumption = proofs.assumption(left, right, label.into());
            let left_to_root = proofs.explain(left, left_root);
            let right_to_root = proofs.explain(right, right_root);
            let root_to_left = proofs.symm(left_to_root);
            let proof = proofs.trans(root_to_left, assumption);
            Some(proofs.trans(proof, right_to_root))
        } else {
            None
        };

        if left_root.raw() == right_root.raw() {
            let dependency = left_root.lift().equalizer(&right_root.lift());
            let common_ambient = left_root.lift().compose(&dependency);
            let common = self.make_restriction(left_root.raw(), dependency);
            let parent = Id::new(dependency, common.raw());
            self.parents[left_root.raw() as usize] = parent;
            if let (Some(proofs), Some(equality)) = (&mut self.proofs, root_equality) {
                let root = Id::new(Lift::identity(left_root.lift().dom()), left_root.raw());
                let proof = proofs.alloc(
                    Endpoint::Raw {
                        raw: root.raw(),
                        lift: root.lift(),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        lift: parent.lift(),
                    },
                    ProofKind::FactorLeft {
                        equality,
                        left: left_root.lift(),
                        common: common_ambient,
                    },
                );
                proofs.link_thinning_equality(left_root.raw(), common.raw(), proof, dependency);
            }
            return true;
        }

        if pullback.diagonal == right_root.lift() {
            let parent = Id::new(pullback.from_left, right_root.raw());
            self.parents[left_root.raw() as usize] = parent;
            if let (Some(proofs), Some(equality)) = (&mut self.proofs, root_equality) {
                let left = Id::new(Lift::identity(left_root.lift().dom()), left_root.raw());
                let proof = proofs.alloc(
                    Endpoint::Raw {
                        raw: left.raw(),
                        lift: left.lift(),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        lift: parent.lift(),
                    },
                    ProofKind::SpecializeLeft {
                        equality,
                        left: left_root.lift(),
                    },
                );
                proofs.link_thinning_equality(
                    left_root.raw(),
                    right_root.raw(),
                    proof,
                    pullback.from_left,
                );
            }
        } else if pullback.diagonal == left_root.lift() {
            let parent = Id::new(pullback.from_right, left_root.raw());
            self.parents[right_root.raw() as usize] = parent;
            if let (Some(proofs), Some(equality)) = (&mut self.proofs, root_equality) {
                let right = Id::new(Lift::identity(right_root.lift().dom()), right_root.raw());
                let proof = proofs.alloc(
                    Endpoint::Raw {
                        raw: right.raw(),
                        lift: right.lift(),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        lift: parent.lift(),
                    },
                    ProofKind::SpecializeRight {
                        equality,
                        right: right_root.lift(),
                    },
                );
                proofs.link_thinning_equality(
                    right_root.raw(),
                    left_root.raw(),
                    proof,
                    pullback.from_right,
                );
            }
        } else {
            let common = self.make_restriction(left_root.raw(), pullback.from_left);
            let left_parent = Id::new(pullback.from_left, common.raw());
            let right_parent = Id::new(pullback.from_right, common.raw());
            self.parents[left_root.raw() as usize] = left_parent;
            self.parents[right_root.raw() as usize] = right_parent;
            if let (Some(proofs), Some(equality)) = (&mut self.proofs, root_equality) {
                let left = Id::new(Lift::identity(left_root.lift().dom()), left_root.raw());
                let left_proof = proofs.alloc(
                    Endpoint::Raw {
                        raw: left.raw(),
                        lift: left.lift(),
                    },
                    Endpoint::Raw {
                        raw: left_parent.raw(),
                        lift: left_parent.lift(),
                    },
                    ProofKind::FactorLeft {
                        equality,
                        left: left_root.lift(),
                        common: pullback.diagonal,
                    },
                );
                let right = Id::new(Lift::identity(right_root.lift().dom()), right_root.raw());
                let right_proof = proofs.alloc(
                    Endpoint::Raw {
                        raw: right.raw(),
                        lift: right.lift(),
                    },
                    Endpoint::Raw {
                        raw: right_parent.raw(),
                        lift: right_parent.lift(),
                    },
                    ProofKind::FactorRight {
                        equality,
                        right: right_root.lift(),
                    },
                );
                proofs.link_thinning_equality(
                    left_root.raw(),
                    common.raw(),
                    left_proof,
                    pullback.from_left,
                );
                proofs.link_thinning_equality(
                    right_root.raw(),
                    common.raw(),
                    right_proof,
                    pullback.from_right,
                );
            }
        }
        true
    }

    pub fn equivalent(&mut self, left: Id, right: Id) -> bool {
        self.find(left) == self.find(right)
    }

    pub fn proof_step_count(&self) -> usize {
        self.proofs.as_ref().map_or(0, |proofs| proofs.arena.len())
    }

    fn proof(&mut self, left: &str, right: &str) -> Result<ProofId, ProofError> {
        let left_raw = *self
            .memo
            .get(left)
            .ok_or_else(|| ProofError::UnknownName(left.to_owned()))?;
        let right_raw = *self
            .memo
            .get(right)
            .ok_or_else(|| ProofError::UnknownName(right.to_owned()))?;
        let left_id = Id::new(Lift::identity(self.arities[left_raw as usize]), left_raw);
        let right_id = Id::new(Lift::identity(self.arities[right_raw as usize]), right_raw);
        if left_id.ctx() != right_id.ctx() {
            return Err(ProofError::Unsupported(
                "certificate endpoints have different arities".to_owned(),
            ));
        }
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
        let raw_equality = proofs.explain(left_id, right_id);
        let left_to_right_raw = proofs.trans(left_memo, raw_equality);
        let right_raw_to_name = proofs.symm(right_memo);
        Ok(proofs.trans(left_to_right_raw, right_raw_to_name))
    }

    /// Print a complete Lean theorem proving pointwise equality in the terms' context.
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
                    " (h{index} : {})",
                    self.relation_type(&node.left, &node.right, false)
                ));
            }
        }
        let arity = self.arities[self.memo[left] as usize];
        let left_endpoint = Endpoint::Named {
            name: left.to_owned(),
            lift: Lift::identity(arity),
        };
        let right_endpoint = Endpoint::Named {
            name: right.to_owned(),
            lift: Lift::identity(arity),
        };
        output.push_str(&format!(
            " : {} := by\n",
            self.relation_type(&left_endpoint, &right_endpoint, false)
        ));
        let mut live_terms = vec![false; self.definitions.len()];
        for (is_live, node) in live.iter().zip(&proofs.arena) {
            if *is_live {
                for endpoint in [&node.left, &node.right] {
                    if let Endpoint::Raw { raw, .. } = endpoint {
                        self.mark_term(*raw, &mut live_terms);
                    }
                }
            }
        }
        for (id, is_live) in live_terms.into_iter().enumerate() {
            if is_live {
                let expression = self.definition_expression(id as RawId, true);
                output.push_str(&format!("  let e{id} := {expression}\n"));
            }
        }
        for (index, node) in proofs.arena.iter().enumerate() {
            if !live[index] {
                continue;
            }
            let expression = match node.kind {
                ProofKind::Refl => {
                    Self::pointwise(Self::endpoint_arity(&node.left), "rfl".to_owned())
                }
                ProofKind::Symm(proof) => {
                    let arguments = Self::variables(Self::endpoint_arity(&node.left));
                    Self::pointwise(
                        arguments.len(),
                        format!("Eq.symm ({})", Self::apply_proof(proof, &arguments)),
                    )
                }
                ProofKind::Trans(first, second) => {
                    let arguments = Self::variables(Self::endpoint_arity(&node.left));
                    Self::pointwise(
                        arguments.len(),
                        format!(
                            "Eq.trans ({}) ({})",
                            Self::apply_proof(first, &arguments),
                            Self::apply_proof(second, &arguments)
                        ),
                    )
                }
                ProofKind::Lift { proof, lift } => Self::pointwise(
                    lift.cod(),
                    Self::apply_proof(proof, &Self::selected_arguments(lift)),
                ),
                ProofKind::SpecializeLeft { equality, left } => Self::pointwise(
                    left.dom(),
                    Self::apply_proof(equality, &Self::filled_arguments(left)),
                ),
                ProofKind::SpecializeRight { equality, right } => Self::pointwise(
                    right.dom(),
                    format!(
                        "Eq.symm ({})",
                        Self::apply_proof(equality, &Self::filled_arguments(right))
                    ),
                ),
                ProofKind::FactorLeft {
                    equality,
                    left,
                    common,
                } => {
                    let original = Self::apply_proof(equality, &Self::filled_arguments(left));
                    let restricted =
                        Self::apply_proof(equality, &Self::subset_arguments(left, common));
                    Self::pointwise(
                        left.dom(),
                        format!("Eq.trans ({original}) (Eq.symm ({restricted}))"),
                    )
                }
                ProofKind::FactorRight { equality, right } => Self::pointwise(
                    right.dom(),
                    format!(
                        "Eq.symm ({})",
                        Self::apply_proof(equality, &Self::filled_arguments(right))
                    ),
                ),
                ProofKind::Assumption { index, ref label } => {
                    output.push_str(&format!("  -- {label}\n"));
                    format!("h{index}")
                }
            };
            output.push_str(&format!(
                "  let p{index} : {} := {expression}\n",
                self.relation_type(&node.left, &node.right, true)
            ));
        }
        output.push_str(&format!("  exact p{}\n", conclusion.0));
        Ok(output)
    }

    fn endpoint_value(&self, endpoint: &Endpoint, local: bool) -> String {
        match endpoint {
            Endpoint::Named { name, lift } => {
                let arguments = Self::selected_arguments(*lift);
                if arguments.is_empty() {
                    name.clone()
                } else {
                    Self::apply(&format!("({name})"), &arguments)
                }
            }
            Endpoint::Raw { raw, lift } => {
                let source = if local {
                    format!("e{raw}")
                } else {
                    self.definition_expression(*raw, false)
                };
                let arguments = Self::selected_arguments(*lift);
                if arguments.is_empty() {
                    source
                } else {
                    Self::apply(&format!("({source})"), &arguments)
                }
            }
        }
    }

    fn endpoint_arity(endpoint: &Endpoint) -> usize {
        match endpoint {
            Endpoint::Named { lift, .. } | Endpoint::Raw { lift, .. } => lift.cod(),
        }
    }

    fn relation_type(&self, left: &Endpoint, right: &Endpoint, local: bool) -> String {
        let arity = Self::endpoint_arity(left);
        assert_eq!(arity, Self::endpoint_arity(right));
        let equality = format!(
            "{} = {}",
            self.endpoint_value(left, local),
            self.endpoint_value(right, local)
        );
        if arity == 0 {
            equality
        } else {
            format!("∀ {}, {equality}", Self::variables(arity).join(" "))
        }
    }

    fn mark_term(&self, raw: RawId, live: &mut [bool]) {
        if std::mem::replace(&mut live[raw as usize], true) {
            return;
        }
        if let Definition::Restrict { source, .. } = self.definitions[raw as usize] {
            self.mark_term(source, live);
        }
    }

    fn definition_expression(&self, raw: RawId, local: bool) -> String {
        match &self.definitions[raw as usize] {
            Definition::Named(name) => name.clone(),
            Definition::Restrict { source, thinning } => {
                let source = if local {
                    format!("e{source}")
                } else {
                    format!("({})", self.definition_expression(*source, false))
                };
                let body = Self::apply(&source, &Self::filled_arguments(*thinning));
                Self::lambda(thinning.dom(), &body)
            }
        }
    }

    fn selected_arguments(lift: Lift) -> Vec<String> {
        (0..lift.cod())
            .filter(|&index| lift.get(index))
            .map(|index| format!("x{index}"))
            .collect()
    }

    fn filled_arguments(thinning: Lift) -> Vec<String> {
        let mut selected = 0;
        (0..thinning.cod())
            .map(|index| {
                if thinning.get(index) {
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
        arguments
            .iter()
            .fold(function.to_owned(), |term, argument| {
                format!("{term} {argument}")
            })
    }

    fn apply_proof(proof: ProofId, arguments: &[String]) -> String {
        arguments
            .iter()
            .fold(format!("p{}", proof.0), |term, argument| {
                format!("{term} {argument}")
            })
    }

    fn variables(arity: usize) -> Vec<String> {
        (0..arity).map(|index| format!("x{index}")).collect()
    }

    fn lambda(arity: usize, body: &str) -> String {
        if arity == 0 {
            body.to_owned()
        } else {
            let variables = (0..arity)
                .map(|index| format!("x{index}"))
                .collect::<Vec<_>>()
                .join(" ");
            format!("(fun {variables} => {body})")
        }
    }

    fn pointwise(arity: usize, body: String) -> String {
        if arity == 0 {
            body
        } else {
            format!("fun {} => {body}", Self::variables(arity).join(" "))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use std::process::{Command, Stdio};

    #[test]
    fn partial_lift_reverses_by_swapping_its_two_lifts() {
        let partial = PartialLift::new(Lift::selected(3, &[0, 2]), Lift::selected(4, &[1, 3]));
        assert_eq!(std::mem::size_of::<PartialLift>(), 8);
        assert_eq!(partial.reverse().source, partial.target);
        assert_eq!(partial.reverse().target, partial.source);
        assert_eq!(partial.reverse().reverse(), partial);
    }

    #[test]
    fn partial_lift_composition_uses_the_middle_pullback() {
        let first = PartialLift::new(Lift::selected(3, &[0, 2]), Lift::selected(4, &[1, 3]));
        let second = PartialLift::new(Lift::selected(4, &[1, 3]), Lift::selected(3, &[0, 2]));
        let composite = first.then(&second);
        assert_eq!(composite.source, Lift::selected(3, &[0, 2]));
        assert_eq!(composite.target, Lift::selected(3, &[0, 2]));
    }

    #[test]
    fn completed_partial_lift_finishes_to_one_lift() {
        let lift = Lift::selected(3, &[0, 2]);
        assert_eq!(PartialLift::total(lift).finish(), lift);
    }

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
    fn dependency_pruning_constructs_a_witness_and_checks_in_lean() {
        let mut union_find = ProofUnionFind::new(true);
        let f = union_find.make_set_with_arity("f", 1);
        let g = union_find.make_set_with_arity("g", 1);
        let f_of_x = union_find.place(f, 2, &[0]);
        let g_of_y = union_find.place(g, 2, &[1]);

        assert!(union_find.union(f_of_x, g_of_y, "f(x) equals g(y)"));
        assert!(union_find.equivalent(f, g));
        assert_eq!(
            union_find
                .proofs
                .as_ref()
                .unwrap()
                .explain_edges
                .iter()
                .flatten()
                .count(),
            2
        );
        assert!(
            union_find
                .proofs
                .as_ref()
                .unwrap()
                .explain_edges
                .iter()
                .flatten()
                .any(|edge| edge.reversed),
            "the example should exercise a rerooted lift edge"
        );

        let certificate = union_find
            .lean_proof(
                "dependency_pruning",
                "{α : Type} [Inhabited α] (f g : α → α)",
                "f",
                "g",
            )
            .unwrap();
        assert!(certificate.contains("default"));
        assert!(!certificate.contains("funext"));
        assert!(!certificate.contains("congrFun"));
        assert!(certificate.contains("∀ x0, (f) x0 = (g) x0"));

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
            "Lean rejected the thinning certificate:\n{certificate}\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn equalizing_two_placements_prunes_one_raw_term() {
        let mut union_find = ProofUnionFind::new(true);
        let f = union_find.make_set_with_arity("f", 1);
        let f_of_x = union_find.place(f, 2, &[0]);
        let f_of_y = union_find.place(f, 2, &[1]);

        assert!(union_find.union(f_of_x, f_of_y, "f(x) equals f(y)"));
        assert!(union_find.equivalent(f_of_x, f_of_y));
        assert_eq!(union_find.find(f).lift().dom(), 0);
    }
}
