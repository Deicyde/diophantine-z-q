# local-glue (2026-11-13)

**Verdict.** `LocalGlue p Tm a β L` (local-data), copied verbatim, is a predicate on arbitrary data
and is false for some (`not_localGlue_zero`, compiled). On G7's data it is a theorem, and on
g0-mod-field's construction of that data no local glue Prop remains.

- General form: `G15Ram.localGlue_of_unramRoots (hR6) (hTors) (hU : UnramRoots p ℓ) (p ≠ ℓ)
  (G7Out) (G7Clauses) (KerWild) (p ≤ 5 → DescentPts A L) : LocalGlue …`.
- Construction form: `G15Ram.localGlue_of_baseChange` for `A = (A₀)_{L'}` (`TateBridge`'s base
  change), with `dim A₀ = 2`, `G7Data`'s kernel-field clause, and `β = ι ∘ β_ℂ` with `ι`
  injective. It rests only on:
  - the leaves R6 and I2-Tors (already in the bundles);
  - the textbook Prop `UnramRoots` (an unramified 4th root of an unramified character), used
    only at `p = 2`.
  `KerWild` comes from `kerWild_of_g7Data`. `DescentPts` comes from `descentPts_baseChange`,
  which builds the conjugate model `A₀ ×_{L,γ} L` needed because of Mathlib's embedding choices.
- At `p ≥ 7` (including `p > D`), only R6 and I2-Tors are used. T16, D3 and Herbrand are not
  needed at all.

**Compiles (VERIFIED).** `scratch/local-glue/LocalGlue.lean` (build.sh) exits 0 with no `sorry`;
all 77 `#print axioms` lines are standard. `TailK.lean` (build_tail.sh) exits 0 with no `sorry`.
The packs and tail are restated on the construction: `G7LocalPackBC`, `g8LocalPack_of_BC`,
`g15RamG_of_packBC`, `modularConstituent_tail_BC`.

Main new proofs:
- `raynaudPlace_of_R6`, `ptFinite`;
- `torsFix_of_descent`: Glazer's `L_v(A_L[m])`, via infinite Galois theory;
- `betaTwist2_of_roots`, `beta4Inertia_of_clauses`;
- `descentPts_baseChange`, `kerWild_of_g7Data`.

**Remains.**
1. `UnramRoots`: Mathlib lacks unramified extensions of `p`-adic fields with a Frobenius generator.
2. Integration: `TateBridge` should also output `β' = ι ∘ β` with `ι` injective (finding G8).
   Then its data fills `G7LocalPackBC`.

Report: docs/research/local-glue.md. Log: scratch/local-glue/log.md.
