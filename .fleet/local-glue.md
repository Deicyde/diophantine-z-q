# local-glue (2026-11-13)

**Verdict.** `LocalGlue p Tm a β L` (local-data), copied verbatim, is a predicate on arbitrary data
and is false for some (`not_localGlue_zero`, compiled). On G7's data it is a theorem:

`G15Ram.localGlue_of_unramRoots (hR6 : RaynaudCriterion) (hTors : TorsionStructure)
(hU : UnramRoots p ℓ) (p ≠ ℓ) (h7 : G7Out …) (hC : G7Clauses β ε L) (hK : KerWild K β L)
(hD : p ≤ 5 → DescentPts A L) : LocalGlue p Tm a β L`

The inputs:
- two leaves already in the bundles: R6 and I2-Tors;
- one textbook Prop, `UnramRoots`: an unramified 4th root of an unramified character. It is used
  only at `p = 2`;
- two glue Props:
  - `KerWild`: G7Data's kernel-field clause, which `G7Out`/`TateBridge` dropped;
  - `DescentPts`: `A` is the base change of a model over `L`. It is used only at `p ≤ 5`.

At `p ≥ 7` (including `p > D`), nothing beyond R6 and I2-Tors is needed. T16, D3 and Herbrand are
not needed at all.

**Compiles (VERIFIED).** `scratch/local-glue/LocalGlue.lean` (build.sh) exits 0 with no `sorry`;
all 72 `#print axioms` lines are standard. `TailK.lean` (build_tail.sh) exits 0 with no `sorry`.
The packs and tail are restated on these inputs: `G7LocalPackU`, `g8LocalPack_of_U`,
`g15RamG_of_packU`, `modularConstituent_tail_U`.

New proofs in this run:
- `raynaudPlace_of_R6`: R6 at the place of `embP`, through a base change to `K(A[m])`;
- `torsFix_of_descent`: Glazer's `E = L_v(A_L[m])` with `[E:L_v] ≤ |GL₄(𝔽_m)|`, via infinite
  Galois theory;
- `betaTwist2_of_roots`;
- `beta4Inertia_of_clauses`: `β⁴ = 1` on inertia at `2`, from `χ` mod `chiLevel`;
- `ptFinite`.

**Remains.**
1. `UnramRoots`: Mathlib lacks unramified extensions of `p`-adic fields with a Frobenius generator.
2. `KerWild`: add it to `TateBridge`'s output (finding G8), then transport from G7Data.
3. `DescentPts`: prove it for `A = (A_L)_{L'}` via `bcPt`/`trPt`, allowing the conjugate model
   when Mathlib's embedding choices differ.

Report: docs/research/local-glue.md. Log: scratch/local-glue/log.md.
