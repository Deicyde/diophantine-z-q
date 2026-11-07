# Report: node-check (the finite check `HaltingNodeCheck`)

Branch `wip/node-check`. Kernel work in `ZInQKernel/Compiler/NodeCheck/` (root
`ZInQKernel/Compiler/NodeCheck.lean`, imported from `ZInQKernel.lean`). Native evaluation in
the separate library `ZInQFinite` (`ZInQFinite.lean`, `ZInQFinite/NodeCheck.lean`, declared as
its own `lean_lib` in `lakefile.toml`, not imported by `ZInQKernel`).

## Summary

- **Milestone 1: done.** `ZInQ.Compiler.Universal.haltingNodeCheck_native : HaltingNodeCheck`
  (in `ZInQFinite`). The native evaluation takes 16.1 s; the whole `ZInQFinite.NodeCheck`
  module builds in about 35 s (it holds two native checks).
- **Milestone 2: partial.** Three of the five items of `HaltingNodeCheck` are proved in the
  kernel without evaluating the construction: the variable count `54,049`, the constant count
  `6` and the constant list `[0, 1, 2, 4, 1399, -1]`. `HaltingNodeCheck` is reduced in the
  kernel to the smaller named check `NodeCheck.HaltingAddMulCheck` (the addition count
  `125,307` and the multiplication count `98,361`). That check is proved natively in
  `ZInQFinite` (`haltingAddMulCheck_native`) and is **not** proved in the kernel.
- My measurements show that running the builder in a single kernel declaration (route (a)) is
  out of reach at a reasonable cost. Running the fast builder alone, with no hash-consing
  table, already needs 20.5 GB of memory and 77 s. The trie table adds about 190 KB per node,
  so the full run would need roughly 70 GB and more than 10 minutes. Details below.

## Table

| article path | Lean name | status |
|---|---|---|
| compiler/natural/universal/halting-node-check.md, item 1 (milestone 1) | `ZInQ.Compiler.Universal.haltingNodeCheck_native` (ZInQFinite) | proved (`native_decide` on the verified fast builder) |
| same, item 1 (milestone 2): reduction | `ZInQ.Compiler.NodeCheck.haltingNodeCheck_of_addMul : HaltingAddMulCheck → HaltingNodeCheck` | proved (kernel) |
| same, item 1: variable count `54,049` | `ZInQ.Compiler.NodeCheck.haltingCircuit_varNodes` | proved (kernel, symbolic) |
| same, item 1: constant count `6` | `ZInQ.Compiler.NodeCheck.haltingCircuit_constNodes` | proved (kernel, symbolic) |
| same, item 1: constants `0,1,2,4,1399,-1` in node order | `ZInQ.Compiler.NodeCheck.haltingCircuit_constList` | proved (kernel, symbolic) |
| same, item 1: additions `125,307`, multiplications `98,361` | `ZInQ.Compiler.NodeCheck.HaltingAddMulCheck` (named finite check) | proved natively only (`ZInQ.Compiler.Universal.haltingAddMulCheck_native`, ZInQFinite); not done in the kernel |
| same, item 1, kernel proof of `HaltingNodeCheck` | `haltingNodeCheck` | not done |

The call count and the first two nodes were already proved on main (`haltingCircuit_counts`,
`haltingCircuit_nodes_eq`); item 2 (power template) was already a kernel proof.

## Statement corrections

None to the statements. One correction to the plan: `HaltingNodeCheck` cannot be proved by
`native_decide` directly. The builder's expressions `Ex` carry `MvPolynomial` fields, which are
noncomputable, so `haltingCircuit` has no compiled code. Even if they were computable, building
the polynomials would blow up. `haltingNodeCheck_native` therefore goes through the verified
poly-free builder: `haltingNodeCheck_of_checkB (by native_decide)`, where the Boolean
`haltingNodeCheckB` runs the fast builder.

## What was built (lemmas beyond the leaf), namespace `ZInQ.Compiler.NodeCheck`

- `NodeCheck/Trie.lean`: binary tries `NTrie` keyed by `Nat`, with `find_insert` (any fuel
  above the key suffices). `find` and `ins` are written with `NTrie.rec`/`Nat.rec` and `Nat`
  primitives, which the kernel reduces about twice as fast as the structural versions. They are
  compiled through the `@[csimp]` lemmas `find_eq_findS` and `ins_eq_insS`, which are proved
  equalities, not `implemented_by`. Also: the node keys `nodeKey` (`key_inj`: injective on
  non-call nodes, via `Nat.pair`), `tabled`, and the table `Table` with `Table.find_insert`.
- `NodeCheck/Builder.lean`: the fast builder. It is a state monad `FM` over `FState` (counter,
  table, length, reversed node list), and its formulas `FForm` keep only node indices
  (`eraseF`). Variable nodes are appended without lookup. The simulation judgment
  `Sim er m m'` is built from the relation `Rel` (same counter, same node list, the table
  answers like `List.idxOf?`, variable indices below the counter, and as many variable nodes as
  explicit variables). It comes with `Sim.bind`, `Sim.pure`, `Sim.note_bind` and the tactic
  `sim_tac`. There is a `*_sim` lemma for every primitive and for every hierarchical-mode macro
  (`lt`, `odd`, `power`, `binomial`, `orthogonal`, `mask`, `bitAnd`), and for the encoding
  (`encode_sim`, `encodeList_sim`).
- `NodeCheck/Packed.lean`: the fast packed construction (items 1–7) with `*_sim` lemmas, and
  `compiled_nodes : (Packed.compiled p r k).nodes = (fastNodesRev p r k).reverse` for every
  program. Also `compiled_varNodes` (variable nodes = explicit variables, for every program).
- `NodeCheck/Check.lean`: a counting pass `countGo` that forces each counter as it goes
  (`countGo_eq`), the Boolean `haltingNodeCheckB`, its soundness `haltingNodeCheck_of_checkB`,
  and `haltingCircuit_varNodes`. The soundness proof is stated for a variable list and then
  instantiated. A first version that worked on the closed list made the kernel evaluate the
  builder: `0 + countKind …` against `countKind …` triggers the GMP reduction.
- `NodeCheck/Fast.lean`: a kernel-friendly version of the fast construction, `constructionK`,
  proved equal to it (`constructionK_eq`, `fastNodesRevK_eq`). The handles of items 6 and 7
  are read from buckets filled in one pass over the program (`bucketGet_buckets`,
  `incHandles_eq`, `decHandles_eq`, `inHandles_eq`), the branch histories from a trie
  (`lookupVW_eq`), and `S` is walked in lockstep. This removes about 1.4·10⁹ kernel list steps
  of `inHandles`.
- `NodeCheck/Consts.lean`: the judgment `CTo S m T` (from constant list `S`, `m` ends with
  constant list `T`) and the tactic `cto_tac`. All gadgets and macros request only `0, 1, 2`;
  item 1 requests `2, 4, m` (`cto_items1`); the encoding requests `-1` (`cto_encode`, with
  `hasEq_construction` proved by `rfl`). This gives `compiled_constList` (constants
  `0,1,2,4,m,-1` for every program with `4 < m`), `haltingCircuit_constList` and
  `haltingCircuit_constNodes`.
- `NodeCheck/Reduced.lean`: `HaltingAddMulCheck`, `haltingNodeCheck_of_addMul`,
  `haltingAddMulCheckB` and `haltingAddMulCheck_of_checkB`.

All kernel theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. No `sorry`,
no `native_decide` in `ZInQKernel`.

## Measurements (kernel = `decide +kernel`; memory = peak RSS; the import baseline is 6.9 GB)

| instance | builder | kernel time | memory |
|---|---|---|---|
| 3-instruction program, r = 2, k = 1 (847 nodes) | original list builder `Packed.compiled` | 73.6 s | |
| same | fast builder (structural trie, naive handles) | 1.28 s | |
| same | `fastNodesRevK` (recursor trie, buckets) | 0.64 s | |
| first 100 instructions of `𝒰`, r = 204 (62,641 nodes) | `fastNodesRevK` | 90 s | 21.6 GB |
| first 300 instructions of `𝒰`, r = 204 (96,217 nodes) | `fastNodesRevK` | 172 s | |
| full `𝒰` without hash-consing table (361,635 nodes) | lower bound for any single-declaration run | 76.6 s | 20.5 GB |
| trie microbenchmark: 5,000 / 20,000 random 39-bit keys (find + insert) | recursor trie | 5.1 s / 55 s | +0.8 / +3.7 GB |
| trivial `Nat` loop, 300,000 iterations | | 11.5 s | +1.9 GB |

- The kernel keeps every intermediate term in its caches for the whole declaration. That is
  about 6 KB per loop iteration and about 600 bytes per reduction step. The fast builder
  without a table costs about 38 KB per node. The binary trie (keys of about 39 bits; one find
  and one insert per node) adds about 190 KB per node, and its time grows faster than linearly.
- Extrapolated full run of `fastNodesRevK`: more than 10 minutes and roughly 70 GB. Variants I
  measured did not help: hashing to 18-bit buckets, a combined find-and-insert walk, and a
  16-ary trie (same time as binary).
- Conclusion: route (a) as a single declaration needs at least 20 GB of memory even with a
  free table. I did not commit it. Route (b), or a split across many declarations, is needed;
  see the suggestions.

## Problems

- `HaltingNodeCheck` itself is not proved in the kernel. Only the reduction to
  `HaltingAddMulCheck` and three of its five items are kernel proofs.
- Downstream (`precisionShape_of` and the `Pstar_*` bounds) still takes `HaltingNodeCheck` as a
  hypothesis. With this branch it can be discharged in two ways: by
  `haltingNodeCheck_of_addMul h`, where `h : HaltingAddMulCheck` is the smaller trusted input,
  or by `haltingNodeCheck_native` in `ZInQFinite`.
- Kernel pitfalls I hit, now avoided in the code. A soundness proof stated on the closed
  builder term made the kernel evaluate the builder (deterministic timeout); state such lemmas
  for a variable list and instantiate. A duplicated unevaluated compound argument, such as
  `cond (… f x …) (g (f x)) (g (f x))`, made a 20,000-step kernel loop superlinear; pass forced
  values instead (`Nat.casesOn`).

## Suggestions for the next agent

1. **The kernel proof of `HaltingAddMulCheck` (route (b), compositional).** Facts that make it
   tractable:
   - A node can only be found by a lookup made after its youngest child exists.
   - A macro's internal nodes (nodes with a child created inside the invocation) can only
     collide with internal nodes of the same invocation. Their count is the same for every
     invocation, up to renaming of node indices.
   - The only lookups that can hit across invocations are the top-level node calls and the
     macros' external-only calls: `a + 1` in `lt`, `b + 1` in `mask`, and the constants.
   - Encoding nodes never collide with construction nodes, because they involve the constant
     `-1`, encoding nodes or call nodes.

   Plan:
   - Prove a renaming-invariance simulation for `FM`. The pattern is the same as `Sim` in
     `NodeCheck/Builder.lean`, with a relation carrying an injective renaming of node indices.
   - Compute each top-level macro's counts once by `decide` on a canonical small state.
   - Run a top-level skeleton in the kernel whose table holds only top-level nodes. Its size is
     a few tens of thousands of node calls, against 361k for the full run.

   The emitted call counts are 129,408 additions and 98,727 multiplications; the hits
   (4,101 and 366) are listed in the implementation note.

   Rough size of the skeleton, counted by hand from the definitions:
   - external-only calls: about 1,600 (`b + 1` in the masks) and about 200 (`a + 1` in the
     top-level `lt`);
   - top-level node calls: about 1,400 in item 2, about 600 in item 4, 1,022 in item 5,
     about 2,600 in item 6 and about 5,200 in item 7;
   - top-level atoms of the encoding: about 2,600 atoms, about 5,300 nodes;
   - one square and one chain node per top-level formula: about 5,700 formulas.

   In total about 25–30k node calls, of which perhaps 10–15k need the table. With the
   present trie that is a few GB in one declaration; it can also be split.
2. **Alternative: many declarations.** The kernel frees its caches between declarations. A run
   with an oracle of the hits needs no table and has a small state (counter, length, counts).
   Split it at top-level formula boundaries; encode each chunk's formulas from known starting
   indices. Verify the misses through a Nodup check split by youngest-child ranges, and pass
   cross-chunk hit claims and old nodes as literals. Likely tens of chunk declarations of
   about 1 GB each.
3. If downstream only needs `countKind .add ≤ 125307` and `countKind .mul ≤ 98361` (as the
   implementation note says), consider weakening `HaltingNodeCheck` to those bounds. They follow
   from the emitted counts minus hits whose presence can be shown locally, with no absence
   argument at all.
4. `NodeCheck/Fast.lean` (bucketed handles) and the recursor trie are verified and ready for
   any kernel evaluation of the builder, for example per chunk.
