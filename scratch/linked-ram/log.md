# linked-ram results log

## 2026-11-13 setup
- Merged origin/wip/linked-tate (already in base), origin/wip/lt-goodred, origin/wip/g0-assemble3 (clean).
- Oleans: copied g0-assemble3's built olean chain (LPrefix, TailA-C, E, F; `~/dzq-wt/g0-assemble3/scratch/g0-assemble3/olean/`)
  into scratch/linked-ram/olean/ (gitignored). ZInQKernel imports of the prefix are unchanged between that worktree and this
  one (diff only in Contrib/TYZGenus, GZTheta, ModularForms; not imported). VERIFIED (git diff --stat).
- g0-assemble3 already redid linked-tate's reduction on the corrected G7Data: `GluePieces4` fields 45 `kernelFieldBreaks`,
  46 `tateRamAtThree`, via `UnramTate.linkedRam_of` (part c12, verbatim linked-tate 98b). VERIFIED (read).

## Findings
- F1. `UnramTate.TateRamAtThree` (part c12) is NOT quantified over G7Data: it ranges over all `K ≤ L ≤ L'` and every
  `QML3 K`, with no bound on `[L:ℚ]`. So g0-assemble3's G7Data fix does not reach it; linked-tate's own caveat ("justified
  only for small K") still applies to GluePieces4 field 46. VERIFIED (read c12 L107-118). Truth for unbounded K: SPECULATIVE
  (likely false: inertia image at 3 can be cut out by a field whose upper break exceeds U0 when K's breaks are near U0).

## Step 1: wild-inertia lemmas (test/Wild.lean, Mathlib only) — VERIFIED (compiles, 0 errors)
- `eq_one_of_pow_eq_one`: ξ^k = 1, p ∤ k, ‖ξ−1‖ < 1 in ℚ̄_p ⇒ ξ = 1.
- `wild_fix_root` (W1), `wild_fix_of_pow` (W2: σ wild, σ^k y = y, p ∤ k ⇒ σ y = y; proof: X^k−1 = ∏(X−c) over the
  fixed field of σ, every factor σ−c, c ≠ 1, injective by wildness), `IsWild.pow`, `wild_fix_of_aeval` (W4: roots of a
  ℚ-polynomial of degree < p are fixed; pigeonhole + W2), `wild_fix_of_pow_eq_one` (W5: y^N = 1, p² ∤ N ⇒ fixed).
- Transfer along e : ℚ̄ → ℚ̄_p with e∘g = σ∘e: `fix_of_finrank` ([L:ℚ] < p ⇒ g ∈ G_L), `fix_of_pow_eq_one`,
  `pow_mem_fixing` (L' finite normal ⇒ g^(p^a) ∈ G_{L'} for some a).

## Step 2: olean/Tail.lean (import TailD; TailD.olean built here from g0-assemble3's TailD.lean, 10 s, 0 errors)
- Needed `lake build ZInQKernel.Hypotheses.JHeight …` first (upstream lean/ helpers), as in memory note.
- `UnramTate.KernelFieldBreaksHigh` (clause (ii) of KernelFieldBreaks, p > D), `KernelFieldBreaksLow` (clause (i)),
  `kernelFieldBreaks_of_halves : Low → High → KernelFieldBreaks`, and
  **`kernelFieldBreaksHigh : KernelFieldBreaksHigh` PROVED**. VERIFIED: Tail.lean 0 errors, axioms
  [propext, Classical.choice, Quot.sound] for both.
  Proof: p > D ≥ [L:ℚ] ⇒ decomp σ ∈ G_L (W4 via minpoly); p odd (D ≥ 3); p² ∤ N = chiLevel Tm
  (`not_sq_dvd_chiLevel`) ⇒ cyc N (decomp σ) = 1 (`cyc_decomp_eq_one`, modularCyclotomicCharacter.unique) ⇒ β(g)² = 1;
  ε = 1 on G_L×G_L (InflatedFrom, ε 1 1 = 1) ⇒ β multiplicative on G_L; g^(p^a) ∈ G_{L'} ⇒ β(g)^(p^a) = 1 ⇒ β(g) = 1.
