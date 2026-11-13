# t-different results log

## Step 1 (22:08 PST): statements copied verbatim
- `scratch/t-different/Statements.lean`: PkgI6 lines 5029-5133 and GlueConductor lines 5717-5746 of
  `scratch/h-decomposition/Leaves.lean`, verbatim (only namespace/section wrappers added).
- Compile: `lake env lean scratch/t-different/Statements.lean`: no errors, no warnings (VERIFIED, 65 s).
- Mathlib 4.35 survey (VERIFIED by reading `.lake/packages/mathlib`):
  * `Mathlib/RingTheory/DedekindDomain/Different.lean`: `differentIdeal`, `conductor_mul_differentIdeal`
    (`conductor(x) * 𝔇 = (f'(x))` when `K(x) = L`), `aeval_derivative_mem_differentIdeal`,
    `pow_sub_one_dvd_differentIdeal` (lower bound `e-1`), `not_dvd_differentIdeal_of_intTrace_notMem`,
    `dvd_differentIdeal_iff` (P ∣ 𝔇 iff ramified).  No upper bound, no Hilbert formula.
  * `Mathlib/RingTheory/Conductor.lean`: `conductor_eq_top_of_adjoin_eq_top`.
  * `Mathlib/RingTheory/Invariant/Basic.lean`: `MulSemiringAction.charpoly G b = ∏ g, (X - C (g • b))`.
  * No lower/upper ramification groups, no Herbrand function, no monogenicity of complete DVR
    extensions (Serre III §6 Prop. 12) in Mathlib: grep for herbrand / ramificationGroup / monogenic
    finds nothing relevant.

## Step 2 (22:30 PST): T20 local reduced to monogenicity (compiled)
- `scratch/t-different/HilbertLocal.lean` (VERIFIED: compiles, axioms propext, Classical.choice,
  Quot.sound):
  * `TDifferent.aeval_derivative_minpoly_eq_prod`: for `B/A` with `A`, `B` integrally closed
    domains, `B` finite torsion-free over `A`, `Frac B/Frac A` Galois, and `B = A[x]`:
    `f'(x) = ∏_{σ ≠ 1} (x - σ x)` (`f = minpoly A x`, `σ ∈ B ≃ₐ[A] B`).
  * `TDifferent.mem_inertia_iff_of_adjoin`: if `B = A[x]`, `σ ∈ G_I ↔ σ x - x ∈ I`.
  * `TDifferent.sum_card_sub_one`: `∑_{i<N} (|G_i| - 1) = ∑_{σ≠1} i(σ)`.
  * `TDifferent.hilbertDifferentFormula_of_adjoin_eq_top`: DVRs `A → B`, finite, torsion-free,
    separable and Galois fraction fields, `B = A[x]` ⇒ the conclusion of
    `PkgI6.HilbertDifferentFormula` (no completeness or perfectness used).
  * `PkgI6.hilbertDifferentFormula_of_monogenicDVR : MonogenicDVR → HilbertDifferentFormula`, where
    `MonogenicDVR` = Serre, Corps locaux III §6 Prop. 12 (UNVERIFIED locator): `∃ x, A[x] = B`.

## Step 3 (22:45 PST): T20 local PROVED
- `TDifferent.exists_adjoin_eq_top` (monogenicity, Serre III §6 Prop. 12, UNVERIFIED locator):
  DVRs `A → B`, `B` finite torsion-free over `A`, residue field of `A` perfect ⇒ `∃ x, A[x] = B`.
  Proof: primitive element `α` of `k_B/k_A`, lift `x`, and `x` or `x + π` makes `g(y) ∈ 𝔪 \ 𝔪²`
  (`g` a lift of the minimal polynomial of `α`); then `B = A[y] + 𝔪^j` for all `j` and Nakayama.
  Completeness of `A` is not used.
- `PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula` (the verbatim leaf I6.7 = T20 local),
  VERIFIED: `lake env lean scratch/t-different/HilbertLocal.lean` compiles; axioms propext,
  Classical.choice, Quot.sound.  (Monogenic.lean development file folded in and removed.)
