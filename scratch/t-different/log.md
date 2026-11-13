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

## Step 4: T21 local reduced to a trace statement (compiled)
- `scratch/t-different/DifferentBound.lean` (VERIFIED: compiles; axioms propext, Classical.choice,
  Quot.sound):
  * `TDifferent.map_maximalIdeal_eq_pow`: `𝔪_A B = 𝔪_B ^ e`, `e = Ideal.ramificationIdx (maximalIdeal B) A`.
  * `PkgI6.differentBound_of_trace : TraceContainsRamificationIdx → DifferentBound`, where
    `TraceContainsRamificationIdx` says `∃ z : B, intTrace A B z = (e : A)` (i.e. `e ∈ Tr_{B/A}(B)`),
    and `DifferentBound` is the verbatim leaf I6.6 (T21 local).  Proof: if `e = 0` in `B` the
    right side is `⊥`; else `(e) = 𝔪_A^k`, `𝔇 = 𝔪_B^d`, and `d ≥ e(k+1)` would make
    `(𝔪_A^{k+1})B ∣ 𝔇`, contradicting Mathlib's `not_dvd_differentIdeal_of_intTrace_notMem` with
    `Tr z = e ∉ 𝔪_A^{k+1}`.
- Not proved: `TraceContainsRamificationIdx`.  The standard proof needs a Hensel root of a lift of
  the minimal polynomial of a residue generator in `B` (the maximal unramified subring) and
  transitivity of the trace; Mathlib 4.35 has Hensel only for `IsAdicComplete` rings
  (`IsAdicComplete.henselianRing`) and no completeness of finite modules over complete rings.

## Step 5: T21 local PROVED
- `scratch/t-different/DifferentBound.lean` (VERIFIED: compiles, ~40 s; axioms propext,
  Classical.choice, Quot.sound):
  * `TDifferent.exists_limit`: `B` (finite free over the complete DVR `A`) is `𝔪_A`-adically
    precomplete (coordinates in a basis).
  * `TDifferent.exists_root_of_residue` (Hensel in `B`): `g ∈ A[X]`, `g(x) ∈ 𝔪_B`, `g'(x)` a unit ⇒
    `∃ u, g(u) = 0 ∧ u ≡ x mod 𝔪_B` (Newton iteration `u ↦ u - w g(u)`, limit along `u_{e m}`).
  * `TDifferent.exists_intTrace_eq_ramificationIdx`: `∃ z, intTrace A B z = e` (uses Mathlib's
    deprecated-but-present `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` for `e f = [L:K]`,
    `Module.Basis.traceDual_powerBasis_eq` for Euler's formula, `Algebra.trace_trace`).
  * `PkgI6.differentBound : PkgI6.DifferentBound` (verbatim leaf I6.6 = T21 local).
