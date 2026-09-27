use lambda_microegg::ProofUnionFind;

fn random(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut value = *state;
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn main() {
    let node_count = std::env::args()
        .nth(1)
        .map(|argument| argument.parse().expect("node count must be an integer"))
        .unwrap_or(5_usize);
    assert!(node_count >= 2, "need at least two nodes");

    let mut union_find = ProofUnionFind::new(true);
    let ids = (0..node_count)
        .map(|index| union_find.make_set(format!("x{index}")))
        .collect::<Vec<_>>();

    // Make one fixed pseudorandom spanning tree, then scramble its edge order and direction.
    // Every edge therefore performs a successful union, independent of the chosen order.
    let mut state = 0x6a09_e667_f3bc_c909_u64;
    let mut edges = (1..node_count)
        .map(|node| (node, random(&mut state) as usize % node))
        .collect::<Vec<_>>();
    for index in (1..edges.len()).rev() {
        let other = random(&mut state) as usize % (index + 1);
        edges.swap(index, other);
    }
    for edge in &mut edges {
        if random(&mut state) & 1 == 1 {
            *edge = (edge.1, edge.0);
        }
    }

    for (index, &(left, right)) in edges.iter().enumerate() {
        assert!(union_find.union(
            ids[left],
            ids[right],
            format!("random union {index}: x{left} = x{right}"),
        ));
    }

    let binders = format!(
        "{{α : Type}} ({})",
        (0..node_count)
            .map(|index| format!("x{index}"))
            .collect::<Vec<_>>()
            .join(" ")
            + " : α"
    );
    let certificate = union_find
        .lean_proof(
            &format!("random_uf_{node_count}"),
            &binders,
            "x0",
            &format!("x{}", node_count - 1),
        )
        .expect("the spanning tree connects every node");
    eprintln!(
        "nodes={node_count} arena_steps={} live_assumptions={} live_proofs={} bytes={} lines={}",
        union_find.proof_step_count(),
        certificate.matches("(h").count(),
        certificate
            .lines()
            .filter(|line| line.starts_with("  let p"))
            .count(),
        certificate.len(),
        certificate.lines().count()
    );
    print!("{certificate}");
}
