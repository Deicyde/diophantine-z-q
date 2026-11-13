# t-different: textbook leaves T20, T21, T22 (ramification)

## Verdict

All four local leaf statements are **proved in Lean**, sorry-free, over their verbatim statements
(axioms `propext`, `Classical.choice`, `Quot.sound` only; VERIFIED by `#print axioms`):

| leaf | statement (verbatim, `scratch/h-decomposition/Leaves.lean`) | theorem | file |
|---|---|---|---|
| T20 local (I6.7) | `PkgI6.HilbertDifferentFormula` (line 5092) | `PkgI6.hilbertDifferentFormula` | `scratch/t-different/HilbertLocal.lean` |
| T21 local (I6.6) | `PkgI6.DifferentBound` (line 5080) | `PkgI6.differentBound` | `scratch/t-different/DifferentBound.lean` |
| T22a (I6.8) | `PkgI6.HerbrandQuotient` (line 5105) | `PkgI6.herbrandQuotient` | `scratch/t-different/Herbrand.lean` |
| T22b (I6.9) | `PkgI6.HerbrandTransitivity` (line 5122) | `PkgI6.herbrandTransitivity` | `scratch/t-different/Herbrand.lean` |

**Not proved:** the *global* forms `GlueConductor.HilbertDifferentFormula` and
`GlueConductor.SerreDifferentBound` (Leaves.lean lines 5732, 5741).  These are the forms that
`HSyn.TextbookLeaves` uses for its fields `t20`, `t21` and that `GlueConductor.D1_genuine` consumes.
The fields `t22a : PkgI6.HerbrandQuotient` and `t22b : PkgI6.HerbrandTransitivity` of
`HSyn.TextbookLeaves` are exactly the statements proved here.  h-decomposition.md §2 lists the
local forms of T20, T21 as acceptable alternatives, with the local-to-global transport as a cited
standard step (Serre III §4, I §7); that transport is still not in Lean.

`scratch/t-different/All.lean` contains all four proofs in one deduplicated file (for
integration; compiles, 52 s, same axioms).

Compile (VERIFIED, 2026-11-12, one Lean process at a time):
`lake env lean scratch/t-different/Statements.lean` (6 s), `HilbertLocal.lean` (9 s),
`DifferentBound.lean` (41 s), `Herbrand.lean` (17 s).  A mechanical text comparison (python,
log step 8) confirms that every leaf definition and every definition it uses (`lowerRam`,
`lowerRamR`, `herbrandPhi`, `upperRam`, `lowerRam_tower`) is character-for-character the block in
Leaves.lean, inside `namespace PkgI6` with the same `open IsLocalRing` and the same local
`FractionRing.liftAlgebra` instances.

Side results worth noting (VERIFIED, compiled):
* Neither the T20 proof nor the T22 proof uses `IsAdicComplete (maximalIdeal A) A`
  (`PkgI6.hilbertDifferentFormula_of_dvr`, `TDifferent.herbrand_trans`,
  `TDifferent.herbrand_quotient` have no completeness hypothesis).  So Hilbert's formula and
  Herbrand's theorem hold for any finite extension of DVRs with perfect residue field of `A`
  (e.g. the localization of `𝓞_L` at a prime of the decomposition field), which would let a
  global T20 avoid completions.  The T21 proof uses completeness (Hensel's lemma in `B`).
* Monogenicity `B = A[x]` (Serre, *Corps locaux*, III §6, Prop. 12; UNVERIFIED locator) is proved
  without completeness (`TDifferent.exists_adjoin_eq_top`).

## 1. Mathlib 4.35 inputs (VERIFIED by reading `.lake/packages/mathlib`)

* `Mathlib/RingTheory/DedekindDomain/Different.lean`: `differentIdeal`,
  `conductor_mul_differentIdeal` (`conductor(x)·𝔇 = (f'(x))` when `K(x) = L`),
  `not_dvd_differentIdeal_of_intTrace_notMem`, `pow_sub_one_dvd_differentIdeal`.  No upper bound,
  no Hilbert formula, no ramification groups or Herbrand function anywhere in Mathlib.
* Galois/ramification API used: `Algebra.isInvariant_of_isGalois'`, `IsGaloisGroup.restrictHom`
  (+ `algebraMap_restrictHom_smul`, `restrictHom_surjective`), `IsGaloisGroup.of_isScalarTower`,
  `IsGaloisGroup.card_eq_finrank'`, `Ideal.card_inertia_eq_ramificationIdxIn`,
  `Ideal.ramificationIdxIn_eq_ramificationIdx`, `Algebra.HasSeparableResidueFieldsAt.tower_top`,
  `galRestrict`, `IsGalois.card_aut_eq_finrank`, `IsAdjoinRootMonic.mkOfAdjoinEqTop'`.
* Trace/field API: `Module.Basis.traceDual_powerBasis_eq` (Euler's formula), `Algebra.trace_trace`,
  `Algebra.trace_algebraMap`, `Algebra.algebraMap_intTrace_fractionRing`,
  `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` (**deprecated** since 2026-07-01 but present:
  `e f = [L : K]` for local `B`; an integrator on a newer Mathlib may need its replacement in
  `RingTheory/RamificationInertia/Basic.lean`).
* Analysis: `intervalIntegral.integral_congr_ae`, `setIntegral_indicator`, `Real.volume_real_Ioc`,
  `intermediate_value_Icc`, `IsPrecomplete.prec`, Nakayama `Submodule.le_of_le_smul_of_le_jacobson_bot`.

## 2. T20 (local): proof (`HilbertLocal.lean`)

Serre, *Corps locaux* IV §1 Prop. 4 (UNVERIFIED numbering):
1. `TDifferent.exists_adjoin_eq_top`: a primitive element `α` of `k_B/k_A`; `x` or `x + π` makes
   `g(y) ∈ 𝔪 \ 𝔪²` for a lift `g` of `minpoly α` (Taylor expansion and separability); then
   `B = A[y] + 𝔪^j` for all `j`, and Nakayama over `A` gives `B = A[y]`.
2. `TDifferent.aeval_derivative_minpoly_eq_prod`: `f'(x) = ∏_{σ ≠ 1}(x − σx)` (roots `σx`
   distinct, degree `= |G| = [L:K]`).
3. `TDifferent.mem_inertia_iff_of_adjoin`: `σ ∈ G_I ↔ σx − x ∈ I` when `B = A[x]`.
4. `TDifferent.hilbertDifferentFormula_of_adjoin_eq_top`: `𝔇 = (f'(x)) = ∏ 𝔪^{i_G(σ)}` (conductor
   `= ⊤`), `∑_{σ≠1} i_G(σ) = ∑_{i<N}(|G_i| − 1)` (`sum_card_sub_one`), `G_N = 1` for
   `N = ∑ i_G(σ)`.

## 3. T21 (local): proof (`DifferentBound.lean`)

1. `TDifferent.exists_limit`: `B` (finite free over `A`) is `𝔪_A`-adically precomplete.
2. `TDifferent.exists_root_of_residue` (Hensel in `B`): Newton iteration `u ↦ u − w g(u)`; the
   limit is taken along `u_{e m}` since `𝔪_A B = 𝔪_B^e` (`map_maximalIdeal_eq_pow`).
3. `TDifferent.exists_intTrace_eq_ramificationIdx`: `u` a Hensel root of a monic lift `g` of
   `minpoly_{k_A} α`; `minpoly_A u = g`, `[K(u):K] = f`, `[L:K(u)] = e` (from `e f = [L:K]`);
   Euler's formula gives `Tr_{K(u)/K}(u^{f−1}/g'(u)) = 1`, so `Tr_{L/K}(u^{f−1}/g'(u)) = e`, and
   `u^{f−1}/g'(u) ∈ B` (`g'(u)` is a unit).
4. `PkgI6.differentBound_of_trace`: if `(e) = 𝔪_A^k` and `v_B(𝔇) ≥ e(k+1)` then
   `(𝔪_A^{k+1})B ∣ 𝔇`, contradicting `not_dvd_differentIdeal_of_intTrace_notMem` since
   `Tr(z) = e ∉ 𝔪_A^{k+1}`; if `e = 0` in `B` the right side is `⊥`.

## 4. T22: proof (`Herbrand.lean`)

Serre, *Corps locaux* IV §1 Prop. 3, IV §3 Lemma 5, Props. 14, 15 (UNVERIFIED numbering).
* Abstract layer, for finite groups with filtrations `Γ i` and index function `n`
  (`s ∈ Γ i ↔ i < n s` for `s ≠ 1`); `TDifferent.phiF` is the formula of `PkgI6.herbrandPhi`
  (`herbrandPhi_eq_phiF : … := rfl`):
  - `phiF_formula`: `|Γ_0|(φ(u)+1) = (u+1) + ∑_{s≠1} min(n s, u+1)` for `u ≥ −1`
    (`integral_indicator_Iic`);
  - `coset_min`: for `s'` of maximal `n` in a coset `s'H ≠ H`, `n(s'h) = min(n s', n h)`;
  - `phiF_trans`: for `1 → H → G → Q → 1` with Prop. 3 as hypothesis
    (`|H_0| · n_Q(σ) = ∑_{s↦σ} n_G(s)`), `φ_G = φ_Q ∘ φ_H` on `[−1, ∞)`; the key identity is
    `∑_{s↦σ} min(n_G s, u+1) = |H_0| · min(n_Q σ, φ_H(u)+1)`, and `|G_0| = |H_0||Q_0|` falls out at
    `u = 0`;
  - `herbrand_lemma` (`r(G_u) = Q_{φ_H(u)}`), `exists_phiF_eq` (IVT on the min-formula),
    `sInf_phiF` (`ψ(v)` computed), `upper_map` (`Q^v = r(G^v)`).
* Ring layer: `resHom` = Mathlib's `IsGaloisGroup.restrictHom`, kernel `B ≃ₐ[C] B`
  (`resHom_eq_one_iff`); `isGaloisGroup_tower`; `span_sub_eq_span_prod` (Prop. 3, ideal form:
  `(σy − y)B = (∏_{s↦σ}(x − sx))`, via `f^σ(x) = ∏_{s↦σ}(x − sx)` for `f = minpoly_C x` and the
  two divisibilities); `card_lowerRam_zero` (`|H_0| = e(B/C)`); `tower_data`; `herbrand_trans`;
  `herbrand_quotient` (any `r` satisfying the compatibility `hr` equals `resHom`).

## 5. What remains

* Global forms of T20/T21 (`GlueConductor.*`): needed by `HSyn.TextbookLeaves.t20/t21` and
  `D1_genuine`.  A route for T20 without completions: localize `𝓞_L` at the prime `P_Z` of the
  decomposition field `Z` (a DVR finite over `(𝓞_Z)_{P_Z}` with Galois group `D_P`), apply
  `PkgI6.hilbertDifferentFormula_of_dvr`, and transport with (i) `𝔇` commutes with localization
  (not in Mathlib), (ii) `P_Z/p` unramified (decomposition field), (iii) Mathlib's
  `differentIdeal_eq_differentIdeal_mul_differentIdeal`, (iv) global `G_i` = local `G_i`.
  T21 globally additionally needs Hensel at `P` (completion), or a non-complete proof of
  `e ∈ Tr(B)`.
* Alternatively the integrator can switch `TextbookLeaves.t20/t21` to the local forms proved here
  and keep the transport as the citation h-decomposition.md already records.
