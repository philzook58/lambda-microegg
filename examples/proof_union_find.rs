use lambda_microegg::ProofUnionFind;

fn main() {
    let mut union_find = ProofUnionFind::new(true);
    let a = union_find.make_set("a");
    let b = union_find.make_set("b");
    let c = union_find.make_set("c");
    let _d = union_find.make_set("d");
    let e = union_find.make_set("e");
    let f = union_find.make_set("f");
    union_find.union(a, b, "input equality a = b");
    union_find.union(b, c, "input equality b = c");
    union_find.union(e, f, "irrelevant equality e = f");
    print!(
        "{}",
        union_find
            .lean_proof("uf_larger", "{α : Type} (a b c d e f : α)", "a", "c",)
            .expect("a and c were joined with proof tracking enabled")
    );
}
