# Report: node-bound (the addition and multiplication bound of the halting circuit)

Branch `wip/node-bound`. New modules in `ZInQKernel/Compiler/NodeBound/`. Root module
`ZInQKernel/Compiler/NodeBound.lean`, imported from `ZInQKernel.lean`. Downstream edits are listed
in step 1.

## Summary

- **Step 1 (interface): done.** I added `ZInQ.Compiler.NodeCheck.HaltingAddMulBound`:
  `countKind .add haltingCircuit.nodes ≤ 125307 ∧ countKind .mul haltingCircuit.nodes ≤ 98361`.
  Every theorem on the main chain that took `hN : HaltingNodeCheck` now takes
  `hB : HaltingAddMulBound`.
- **Step 2 (kernel proof): done.** `ZInQ.Compiler.NodeCheck.haltingAddMulBound :
  HaltingAddMulBound` is proved in the kernel. It uses no `native_decide`, evaluates no
  builder, and makes no absence argument. The four-hypothesis theorem
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` no longer has a `sorry`. It is
  `exists_bounded_integer_polynomial_defining_integers_of_addMulBound haltingAddMulBound hH hPC h22 hCAT`.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]`, both for it and for
  `haltingAddMulBound`.
- `HaltingNodeCheck` and `HaltingAddMulCheck` (the exact counts) are unchanged. They are still
  proved only natively, in `ZInQFinite`, and the main theorem no longer depends on them.

## Table

| article path | Lean name | status |
|---|---|---|
| compiler/natural/universal/halting-node-check.md, item 1, the bounds used downstream | `ZInQ.Compiler.NodeCheck.HaltingAddMulBound` (definition), `ZInQ.Compiler.NodeCheck.haltingAddMulBound` | proved (kernel) |
| same, the bound from the exact counts | `ZInQ.Compiler.NodeCheck.haltingAddMulBound_of_check : HaltingAddMulCheck → HaltingAddMulBound` | proved |
| same, item 1, exact counts | `HaltingNodeCheck`, `HaltingAddMulCheck` | unchanged: native only (`ZInQFinite`) |
| compiler/natural/universal/circuit-node-counts.md, the addition and multiplication bounds of the precision circuit | `ZInQ.Compiler.Universal.precisionCircuitOf_addMulBound`, `precisionCircuit_addMulBound` | proved (from `hB`) |
| syntax/literal-polynomial.md | `ZInQ.Syntax.precisionShape_of`, `specPstar_spec`, `specPstar_zero_projection` (now take `hB`) | proved |
| size/majorants/degree-coefficient-bound.md | `ZInQ.Size.PstarNat_maj`, `Pstar_degree_coeff`, `Pstar_size`, `Pstar_target_bounds` (now take `hB`) | proved |
| assembly/assembly-lemma.md | `ZInQ.Assembly.specPstar_zero_projection_valueRel`, `Pstar_spec_of`, `Pstar_spec`, `assembly` (now take `hB`) | proved |
| main theorem | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound` (new), `..._of_nodeCheck` (corollary), `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` (no `sorry`) | proved |
| ZInQFinite | `ZInQ.exists_bounded_integer_polynomial_defining_integers_native` (now through `_of_addMulBound` and `haltingAddMulBound_of_check haltingAddMulCheck_native`) | proved (native; now redundant) |

## Step 1: what changed downstream

- `Compiler/Universal/PrecisionCircuit.lean`: added `precisionCircuitOf_addMulBound` (the bound
  of `ℋ` plus the `20` additions and `21` multiplications of the specialization) and
  `precisionCircuitOf_countKind_call` (`15,845` calls; no node check needed).
  `precisionCircuitOf_nodeStats` and `precisionCircuitOf_constants` still take `hN` and are kept
  as separate statements.
- `Compiler/Universal/WrapperCode.lean`: added `precisionCircuit_addMulBound`. I kept
  `precisionCircuit_nodeStats (hN)`.
- `Syntax/Recipes/Literal.lean`: `precisionShape_of` takes `hB`. Its constant field now comes
  from `precisionCircuitOf_consts` (no node check) through the new lemma
  `precisionCircuitOf_nontrivialConst`; before, it came from the exact constant list of
  `HaltingNodeCheck`. `specPstar_spec` and `specPstar_zero_projection` take `hB`.
- `Size/Majorants/Bound.lean`, `Assembly/Top/Assembly.lean`, `Main.lean`, `ZInQFinite/Main.lean`:
  `hN` replaced by `hB`. The module docs are updated to match.

## Step 2: the proof

The idea is an upper-bound Hoare judgment over the construction monad `Natural.NM`, with
presence facts.

- `Up.lean`: `Up P m a b Q`. From a node list satisfying `P`, `m` only extends the node list,
  creates at most `a` addition and `b` multiplication nodes, and ends in `Q`. The only facts
  used are presence facts (`n ∈ l`, `l.idxOf? n = some i`), which are monotone (`Mono`). Rules:
  `bind`, `pure`, `weaken`, `pre`, `post`. Primitives: `node_add`/`node_mul` (at most one new
  node), `node_hit` (no new node when present), `constant`, `fresh`, `callPower`, `note`.
  `encA`/`encM` give the encoding cost of a formula; `Cost` and `CostL` record it.
- `Macros.lean`: one bound per macro, for all arguments. Tactics `up_run`/`up_norm`/`up_present`
  do the bookkeeping, and each macro takes a few seconds. Bounds (additions, multiplications;
  encoding cost):
  - `lt`: 2, 0; encoding (1, 1).
  - `odd`: 1, 1; encoding (1, 1).
  - `power`: 0, 0; encoding (0, 0).
  - `binomial`: 8, 2, or 7, 2 when `N+1` is present (`binomial_up_succ`); encoding (8, 9).
  - `orthogonal`: 10, 3, or 9, 3 when `a+b` is present (`orthogonal_up_hit`); encoding (10, 12).
  - `mask`: 9, 3, or 8, 3 when `b+1` is present (`mask_up_succ`); encoding (10, 12).
  - `bitAnd`: 30, 9, which already subtracts its 2 internal re-sums; encoding (36, 43).
- `Items.lean`: items 1–5 for every program.
  - The masks of item 3 after the first use `F+1` (`HasSucc`).
  - The register masks of item 4 after the first use `D+1`.
  - Every register of item 4 uses `K·F`, built by item 2.
  - Item 5 records that `V_i + W_i` is present for every branch history.
- `Encode.lean`: the node encoding (`encode_up`, `encodeList_up`). It also proves that a
  repeated right side `b` of a top-level atom re-requests `(-1)·b` (`encodeList_up_dup`,
  counting with `dupGo`).
- `Items67.lean`, `Program67.lean`: items 6 and 7.
  - The handles are read symbolically. `S_i`, `V_i`, `W_i` get the codes `3i+3`, `3i+4`,
    `3i+5`, and zero gets `0`.
  - The real handle lists are the images of the symbolic ones under `codeEx`
    (`inc_corr`, `dec_corr`, `in_corr`). The proof uses only that equal codes give equal
    expressions; it never uses that the codes are distinct.
  - The repeats in item 7, per state:
    - (A) the predecessors start with `V_i', W_i'` of the same sub instruction: one addition
      fewer (37 states);
    - (B) the only predecessor is `S_i'`, and it is also the only summand of some `A_j`: one
      multiplication fewer (140 states);
    - (C) a state `≠ 0` without predecessors, after the first such state: nothing is created
      (11 states, each saving one addition and one multiplication). These 12 states also share
      their right side `0 + B·0`, which gives the 11 encoding hits.
- `Top.lean`: `compiled_bound`. For every program with `m ≥ 1` instructions, `r+1` registers
  and `k` inputs, `𝒞_{p,k}` has at most `addBound p r k` addition and `mulBound p r k`
  multiplication nodes.
- `Check.lean`: the program-dependent parts at `𝒰` by `decide +kernel`. The handle lists come
  from the existing buckets of `NodeCheck/Fast.lean` (`incHandles_eq` and the others). The
  values are `cost6 = 1602`, `cost7A = 2384`, `cost7M = 1248` and `nC7 = 12`, which give
  `addBound 𝒰 203 2 = 125307` and `mulBound 𝒰 203 2 = 98361`.

The accounting matches the implementation note exactly. Additions: 129,408 emitted, minus
2,452 (bitAnd), 1,601 (mask `N+1`) and 48 (item 7), which is 125,307. Multiplications: 98,727
emitted, minus 204 (`K·F`), 151 (item 7) and 11 (encoding), which is 98,361. The note puts the
48 and 151 in "items 6–7". More precisely, all of them are in item 7: 37 additions hit item-5
nodes, 140 multiplications hit item-6 nodes, and the remaining 11 + 11 hit item-7 nodes. I
checked this with a Python transcription of the builder outside the repository. It reproduces
125,307 and 98,361.

## Measurements

`/usr/bin/time -v lake env lean <file>`, one process at a time. Memory is the peak RSS of the
whole process. The import baseline, which mostly maps the imported `.olean` files, is 6.96 GB.

| module | wall time | peak RSS |
|---|---|---|
| `NodeBound/Defs`, `OfCheck` | 4.9 s each | 6.96 GB |
| `NodeBound/Up` | 5.1 s | 7.00 GB |
| `NodeBound/Macros` | 7.5 s | 7.23 GB |
| `NodeBound/Items` | 7.1 s | 7.09 GB |
| `NodeBound/Encode` | 5.7 s | 7.02 GB |
| `NodeBound/Items67`, `Program67` | 5.7 s each | 7.02 GB |
| `NodeBound/Top` | 6.1 s | 7.06 GB |
| `NodeBound/Check` (all four kernel computations) | 24.9 s | 8.64 GB |

Each kernel computation run alone, as wall time and peak RSS minus the 4.96 s / 6.96 GB
baseline:

| declaration | added time | added memory |
|---|---|---|
| `cost6_interpreter` | 1.6 s | +0.28 GB |
| `nC7_interpreter` | 3.8 s | +0.60 GB |
| `cost7A_interpreter` | 5.9 s | +0.98 GB |
| `cost7M_interpreter` | 9.4 s | +1.67 GB |

My additions build in about 80 s in total, well under the 20-minute budget. No declaration
needs more than 1.7 GB over the import baseline. A full incremental `lake build ZInQKernel
ZInQFinite` after my last change took 1:38, with a peak RSS of 12.4 GB, set by modules outside
my directory.

## Statement corrections

- None to the blueprint statements. `HaltingAddMulBound` is a new, weaker interface. The
  downstream statements (`PrecisionShape`) were already stated with upper bounds.
- The implementation note says "Upper bounds from counting constructor calls are not enough".
  That holds only if hits are ignored. Counting emitted calls minus the hits proved by
  presence alone gives the exact bounds, and that is what the proof does.
- The item-2 bound in `items2_up` is `3 + (m - 1)` and not `m + 2`, because the empty sum
  creates no addition. The two agree for `m ≥ 1`. `compiled_bound` assumes `m ≥ 1`.

## Lemmas beyond the leaves (namespace `ZInQ.Compiler.NodeBound` unless noted)

- `Up`, `Mono`, `Cost`, `CostL`, `encA`/`encAL`/`encM`/`encML`, `Up.node_hit` and the other
  primitives, `countKind_append_singleton`.
- Macro bounds: `lt_up`, `odd_up`, `power_up`, `binomial_up`, `binomial_up_succ`,
  `orthogonal_up`, `orthogonal_up_hit`, `mask_up`, `mask_up_succ`, `bitAnd_up`. Also
  `HasSucc` and the tactics `up_run`, `up_norm`, `up_present`, `up_mono`, `mono_tac`.
- Item bounds:
  - items 1–5: `items1_up`, `items2_up`, `items3_up`, `registerMasks_up`,
    `registerMasks_up_succ`, `items4_up`, `subBranches_up`, `decPos`;
  - items 6–7: `registerEq_up`, `stateEq_up`, `stateEq_up_a`, `stateEq_up_b`, `stateEq_up_c`,
    `items6_up`, `stateEq_step`, `items7_go`, `items7_up`;
  - list combinators: `seqM_up`, `seqConcat_up`, `seqM_up_idx`, `addL_up`, `addL_up'`,
    `mulL_up`, `addFrom_up`, `mulFrom_up`, `freshN_up`.
- Encoding: `encode_up`, `encodeList_up`, `encode_eq_up`, `encode_eq_up_hit`,
  `encodeList_up_dup`, `encode_and_up`, `rhsNode`, `dupGo`, `dupGo_le`, `NegMul`,
  `countP_le_dupGo`, `dupGo_ge`.
- Symbolic handles: `sCodes`, `vwCodes`, `symInc`, `symDec`, `symIn`, `codeEx`, `inc_corr`,
  `dec_corr`, `in_corr`, `symLookup`, `realLookup_mem`; the item-7 classifiers and costs
  `isA7`, `isB7`, `isC7`, `step7A`, `step7M`, `cost7A`, `cost7M`, `nC7`, `singles`, `cost6`;
  `ZPre`, `ZPost`, `Pre7`, `Post7`.
- Top level: `packedFormulas_up`, `construction_encode_up`, `compiled_bound`, `addBound`,
  `mulBound`, `itemsA`, `itemsM`, `formA`, `formM`, `formN`.
- Check: `incB`, `decB`, `inB`, `symInc_eq`, `symDec_eq`, `symIn_eq`, `cost6_interpreter`,
  `nC7_interpreter`, `cost7A_interpreter`, `cost7M_interpreter`, `addBound_interpreter`,
  `mulBound_interpreter`.
- In other namespaces: `NodeCheck.haltingAddMulBound_of_check`;
  `Universal.precisionCircuitOf_addMulBound`, `precisionCircuitOf_countKind_call`,
  `precisionCircuit_addMulBound`; `Syntax.precisionCircuitOf_nontrivialConst`.

## Problems

- None blocking.
- Pitfall: in the final arithmetic, `simp only [..., interpreter_length, cost7A_interpreter]`
  rewrote `interpreter.length` before the `cost7A` lemma could match. The leftover goal then
  made the kernel time out after 8 minutes. Ordered `rw` fixes it. Never leave a goal
  containing `cost7A (symIn interpreter) …` to `rfl`, `decide` or the kernel.
- `Macros.lean` imports nothing beyond `NodeBound/Defs`. `Check.lean` imports
  `NodeCheck/Fast.lean` for the buckets, so `Main.lean` now depends on `Compiler/NodeCheck`
  through `Compiler/NodeBound`.

## Suggestions for the next agent

1. The blueprint can mark the bound part of `halting-node-check.md` as proved in the kernel. The
   main theorem no longer needs `HaltingNodeCheck`, so the milestone-1 input becomes optional.
   `ZInQFinite` is now redundant for the main theorem.
2. An exact kernel proof of `HaltingAddMulCheck` (task node-skeleton) would also need the
   absence direction. The `Up` judgment gives the upper half. A lower-bound twin (every miss of
   the symbolic run is a real miss) would need distinctness of the codes and injectivity of the
   node keys (`NodeCheck.key_inj`).
3. The `Up` framework applies to any other hash-consed construction whose node counts enter a
   bound, for example the precision circuit's own templates. Its macros take seconds.
