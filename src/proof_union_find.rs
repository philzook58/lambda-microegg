//! Standalone proof-producing union-find experiment.
//!
//! Lambda Micro Egg's `EGraph` does not use this implementation. It is kept for the
//! Oliveras-style explanation-forest tests, examples, and measurements that guided
//! the e-graph proof recorder. Production e-graph proof generation lives in `proof.rs`.
//!
//! The thinning experiment is deliberately single-sorted. An entry of arity `n`
//! denotes a curried Lean function `α → ... → α` with `n` inputs; an ordinary
//! constant has arity zero. Dumping a term to a smaller context fills every removed
//! input with `default`, so generated theorems that prune dependencies require
//! `[Inhabited α]`.

use rustc_hash::FxHashMap as HashMap;

use crate::proof::{ProofError, ProofId};
use crate::{Id, Lift, RawId};

/// Substitution of a smaller ambient context into a term's intrinsic context.
///
/// `arguments[i] = Some(j)` sends source argument `i` to ambient variable `j`;
/// `None` fills it with `default`. This is closed under compositions of lift and
/// dump, unlike either operation by itself.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ContextMap {
    ambient_arity: usize,
    arguments: Vec<Option<usize>>,
}

impl ContextMap {
    fn identity(arity: usize) -> Self {
        Self {
            ambient_arity: arity,
            arguments: (0..arity).map(Some).collect(),
        }
    }

    fn lift(thinning: Lift) -> Self {
        Self {
            ambient_arity: thinning.cod(),
            arguments: (0..thinning.cod())
                .filter(|&index| thinning.get(index))
                .map(Some)
                .collect(),
        }
    }

    fn is_identity(&self) -> bool {
        self.arguments.len() == self.ambient_arity
            && self
                .arguments
                .iter()
                .enumerate()
                .all(|(index, argument)| *argument == Some(index))
    }

    /// Apply `outer` after this map.
    fn then(&self, outer: &Self) -> Self {
        assert_eq!(self.ambient_arity, outer.arguments.len());
        Self {
            ambient_arity: outer.ambient_arity,
            arguments: self
                .arguments
                .iter()
                .map(|argument| argument.and_then(|index| outer.arguments[index]))
                .collect(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum MapArgument {
    Known(Option<usize>),
    /// A coordinate discarded by a reversed lift. The path from the other
    /// endpoint may determine it; otherwise certificate printing uses `default`.
    Hole(usize),
}

#[derive(Clone, Debug)]
struct MapTemplate {
    ambient_arity: usize,
    arguments: Vec<MapArgument>,
}

impl MapTemplate {
    fn known(map: ContextMap) -> Self {
        Self {
            ambient_arity: map.ambient_arity,
            arguments: map.arguments.into_iter().map(MapArgument::Known).collect(),
        }
    }

    fn resolve(&self, holes: &mut HoleAssignments) -> ContextMap {
        ContextMap {
            ambient_arity: self.ambient_arity,
            arguments: self
                .arguments
                .iter()
                .map(|argument| match *argument {
                    MapArgument::Known(value) => value,
                    MapArgument::Hole(hole) => holes.value(hole),
                })
                .collect(),
        }
    }
}

#[derive(Default)]
struct HoleAssignments {
    parents: Vec<usize>,
    values: Vec<Option<Option<usize>>>,
}

impl HoleAssignments {
    fn fresh(&mut self) -> MapArgument {
        let hole = self.parents.len();
        self.parents.push(hole);
        self.values.push(None);
        MapArgument::Hole(hole)
    }

    fn root(&mut self, hole: usize) -> usize {
        let parent = self.parents[hole];
        if parent == hole {
            hole
        } else {
            let root = self.root(parent);
            self.parents[hole] = root;
            root
        }
    }

    fn assign(&mut self, hole: usize, value: Option<usize>) {
        let root = self.root(hole);
        if let Some(old) = self.values[root] {
            assert_eq!(old, value, "incompatible explanation context maps");
        } else {
            self.values[root] = Some(value);
        }
    }

    fn unify(&mut self, left: MapArgument, right: MapArgument) {
        match (left, right) {
            (MapArgument::Known(left), MapArgument::Known(right)) => {
                assert_eq!(left, right, "incompatible explanation context maps");
            }
            (MapArgument::Hole(hole), MapArgument::Known(value))
            | (MapArgument::Known(value), MapArgument::Hole(hole)) => self.assign(hole, value),
            (MapArgument::Hole(left), MapArgument::Hole(right)) => {
                let left = self.root(left);
                let right = self.root(right);
                if left != right {
                    let left_value = self.values[left];
                    let right_value = self.values[right];
                    self.parents[right] = left;
                    match (left_value, right_value) {
                        (Some(left), Some(right)) => {
                            assert_eq!(left, right, "incompatible explanation context maps")
                        }
                        (None, Some(value)) => self.values[left] = Some(value),
                        _ => {}
                    }
                }
            }
        }
    }

    fn value(&mut self, hole: usize) -> Option<usize> {
        let root = self.root(hole);
        self.values[root].unwrap_or(None)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Endpoint {
    Named { name: String, map: ContextMap },
    Raw { raw: RawId, map: ContextMap },
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ProofKind {
    Refl,
    Symm(ProofId),
    Trans(ProofId, ProofId),
    Map {
        proof: ProofId,
        map: ContextMap,
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
    left: Endpoint,
    right: Endpoint,
    kind: ProofKind,
}

/// A canonical edge proves `larger = lift(thinning, smaller)`. `reversed`
/// changes which raw node is the forest child; traversal then specializes the
/// larger context with defaults, the proof-producing form of `dump`.
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
                map: ContextMap::lift(left.lift()),
            },
            Endpoint::Raw {
                raw: right.raw(),
                map: ContextMap::lift(right.lift()),
            },
            ProofKind::Assumption { index, label },
        )
    }

    fn map_endpoint(endpoint: &Endpoint, outer: &ContextMap) -> Endpoint {
        match endpoint {
            Endpoint::Named { name, map } => Endpoint::Named {
                name: name.clone(),
                map: map.then(outer),
            },
            Endpoint::Raw { raw, map } => Endpoint::Raw {
                raw: *raw,
                map: map.then(outer),
            },
        }
    }

    fn map_proof(&mut self, proof: ProofId, map: ContextMap) -> ProofId {
        if map.is_identity() {
            return proof;
        }
        let node = &self.arena[proof.0 as usize];
        let left = Self::map_endpoint(&node.left, &map);
        let right = Self::map_endpoint(&node.right, &map);
        self.alloc(left, right, ProofKind::Map { proof, map })
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

    /// Record `larger = lift(thinning, smaller)`. The forest initially points
    /// in the dump direction; subsequent links reroot and flip edges as needed.
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
        let mut holes = HoleAssignments::default();
        let left_maps = Self::plan_path(left, &left_path, &mut holes);
        let right_maps = Self::plan_path(right, &right_path, &mut holes);
        let left_common = left_maps.last().unwrap();
        let right_common = right_maps.last().unwrap();
        assert_eq!(left_common.ambient_arity, right_common.ambient_arity);
        assert_eq!(left_common.arguments.len(), right_common.arguments.len());
        for (&left, &right) in left_common.arguments.iter().zip(&right_common.arguments) {
            holes.unify(left, right);
        }

        let left_to_common = self.materialize_path(left, &left_path, &left_maps, &mut holes);
        let right_to_common = self.materialize_path(right, &right_path, &right_maps, &mut holes);
        let common_to_right = self.symm(right_to_common);
        let proof = self.trans(left_to_common, common_to_right);
        debug_assert_eq!(
            self.arena[proof.0 as usize].right,
            Endpoint::Raw {
                raw: right.raw(),
                map: ContextMap::lift(right.lift()),
            },
            "explanation forest disagrees with operational thinning"
        );
        proof
    }

    fn plan_path(start: Id, path: &[ExplainEdge], holes: &mut HoleAssignments) -> Vec<MapTemplate> {
        let mut maps = vec![MapTemplate::known(ContextMap::lift(start.lift()))];
        for &edge in path {
            let current = maps.last().unwrap();
            let next = if edge.reversed {
                assert_eq!(current.arguments.len(), edge.thinning.dom());
                let mut arguments = Vec::with_capacity(edge.thinning.cod());
                let mut selected = 0;
                for index in 0..edge.thinning.cod() {
                    if edge.thinning.get(index) {
                        arguments.push(current.arguments[selected]);
                        selected += 1;
                    } else {
                        arguments.push(holes.fresh());
                    }
                }
                MapTemplate {
                    ambient_arity: current.ambient_arity,
                    arguments,
                }
            } else {
                assert_eq!(current.arguments.len(), edge.thinning.cod());
                MapTemplate {
                    ambient_arity: current.ambient_arity,
                    arguments: (0..edge.thinning.cod())
                        .filter(|&index| edge.thinning.get(index))
                        .map(|index| current.arguments[index])
                        .collect(),
                }
            };
            maps.push(next);
        }
        maps
    }

    fn materialize_path(
        &mut self,
        start: Id,
        path: &[ExplainEdge],
        maps: &[MapTemplate],
        holes: &mut HoleAssignments,
    ) -> ProofId {
        let endpoint = Endpoint::Raw {
            raw: start.raw(),
            map: maps[0].resolve(holes),
        };
        let mut proof = self.alloc(endpoint.clone(), endpoint, ProofKind::Refl);
        for (index, &edge) in path.iter().enumerate() {
            let mapped = if edge.reversed {
                let outer = maps[index + 1].resolve(holes);
                let mapped = self.map_proof(edge.forward, outer);
                self.symm(mapped)
            } else {
                let current = maps[index].resolve(holes);
                self.map_proof(edge.forward, current)
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
                ProofKind::Symm(child) | ProofKind::Map { proof: child, .. } => work.push(child),
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
                    map: ContextMap::identity(arity),
                },
                Endpoint::Raw {
                    raw,
                    map: ContextMap::identity(arity),
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
                        map: ContextMap::lift(root.lift()),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        map: ContextMap::lift(parent.lift()),
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
                        map: ContextMap::lift(left.lift()),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        map: ContextMap::lift(parent.lift()),
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
                        map: ContextMap::lift(right.lift()),
                    },
                    Endpoint::Raw {
                        raw: parent.raw(),
                        map: ContextMap::lift(parent.lift()),
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
                        map: ContextMap::lift(left.lift()),
                    },
                    Endpoint::Raw {
                        raw: left_parent.raw(),
                        map: ContextMap::lift(left_parent.lift()),
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
                        map: ContextMap::lift(right.lift()),
                    },
                    Endpoint::Raw {
                        raw: right_parent.raw(),
                        map: ContextMap::lift(right_parent.lift()),
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
                ProofKind::Refl => "rfl".to_owned(),
                ProofKind::Symm(proof) => format!("Eq.symm p{}", proof.0),
                ProofKind::Trans(first, second) => {
                    format!("Eq.trans p{} p{}", first.0, second.0)
                }
                ProofKind::Map { proof, ref map } => self.pointwise_proof(
                    map.ambient_arity,
                    Self::apply_proof(proof, &Self::map_arguments(map)),
                ),
                ProofKind::SpecializeLeft { equality, left } => self.pointwise_proof(
                    left.dom(),
                    Self::apply_proof(equality, &Self::filled_arguments(left)),
                ),
                ProofKind::SpecializeRight { equality, right } => self.pointwise_proof(
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
                    self.pointwise_proof(
                        left.dom(),
                        format!("Eq.trans ({original}) (Eq.symm ({restricted}))"),
                    )
                }
                ProofKind::FactorRight { equality, right } => self.pointwise_proof(
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
            Endpoint::Named { name, map } => Self::map_expression(name, map),
            Endpoint::Raw { raw, map } => Self::map_expression(&format!("e{raw}"), map),
        }
    }

    fn endpoint_source(&self, endpoint: &Endpoint) -> String {
        match endpoint {
            Endpoint::Named { name, map } => Self::map_expression(name, map),
            Endpoint::Raw { raw, map } => {
                let source = self.definition_expression(*raw, false);
                let source = if map.is_identity() {
                    source
                } else {
                    format!("({source})")
                };
                Self::map_expression(&source, map)
            }
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

    fn map_expression(base: &str, map: &ContextMap) -> String {
        if map.is_identity() {
            return base.to_owned();
        }
        let body = Self::apply(base, &Self::map_arguments(map));
        Self::lambda(map.ambient_arity, &body)
    }

    fn map_arguments(map: &ContextMap) -> Vec<String> {
        map.arguments
            .iter()
            .map(|argument| match argument {
                Some(index) => format!("x{index}"),
                None => "default".to_owned(),
            })
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
                format!("congrFun ({term}) {argument}")
            })
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

    fn pointwise_proof(&self, arity: usize, body: String) -> String {
        if arity == 0 {
            body
        } else {
            let variables = (0..arity)
                .map(|index| format!("x{index}"))
                .collect::<Vec<_>>()
                .join(" ");
            format!("by\n    funext {variables}\n    exact {body}")
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
    fn dependency_pruning_uses_dump_and_checks_in_lean() {
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
            "the example should exercise a rerooted dump edge"
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
        assert!(certificate.contains("funext"));

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
