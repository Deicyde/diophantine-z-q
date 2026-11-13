# hecke-all results log

## LocalCd.lean (VERIFIED: compiles, `lake build ZInQKernel.Contrib.HeckeAll.LocalCd`, ~22:12; axioms propext, Classical.choice, Quot.sound)
- `isMinimal_baseChange_of_c₄`: integral W over a DVR is minimal if `W.c₄ ≠ r⁴ c₄(W')` for all r ∈ 𝔪, W' integral.
- `c₄_two_adic`: over ℤ₂ (natGenerator v = 2), every integral model has `16 ∣ c₄` (a₁ ∈ 𝔪) or `c₄ ∉ 𝔪`.
- `isMinimal_cdLocal_two`: y² = x³ − (2e)²x is minimal at 2 for odd e (v₂(c₄) = 6).
- `isMinimal_cdLocal'`: y² = x³ − d²x minimal at every place for squarefree d (any parity).
- `hasAdditiveReduction_cdLocal'`, `localPolynomial_cdLocal_eq'`, `LFunction_cd_apply_prime_pow'`,
  `LFunction_cd_apply_prime'`, `LFunction_cd_apply'`, `LFunction_cd_apply_prime_eq_sub_card'`,
  `LFunction_cd_apply_prime_of_dvd'`, `LSeries_cd_eq'`: LFunctionCd.lean's results for every squarefree d.

## Iso.lean (VERIFIED: compiles, `lake env lean`, ~22:15, no errors)
- `not_hasMultiplicativeReduction_smul`: v(c₄)³ ≤ v(Δ) (integral j) ⇒ no model C • W has multiplicative reduction.
- `localPolynomial_eq_ite`, `localPolynomial_smul`: Mathlib's `localPolynomial` is invariant under any change of
  variables when j is integral (both minimal models differ by v(u) = 1; good/additive classes and #W̃(κ) agree).
- `hj_cdLocal` (c₄³ = 1728Δ for C_d), `scaleChange`, `scaleChange_smul`, `LFunction_cd_sq_mul`,
  `LSeries_cd_sq_mul`: L(C_{m²d}, s) = L(C_d, s) for d, m ≠ 0.

## Continuation.lean (VERIFIED: `lake build ZInQKernel.Contrib.HeckeAll.Continuation`, ~22:18; axioms propext, Classical.choice, Quot.sound)
- `jacobiSym_mul_right_all`, `jacobiSym_factorization`: J(a | ·) completely multiplicative (incl. 0).
- `eulerCoeff d p k` = [T^k] 1/cdEulerPoly d p; `eulerCoeff_cast`, `eulerCoeff_of_dvd`, `eulerCoeff_zero`.
- `cdEulerPoly_twist` (p ∤ 2d: a_p(C_d) = J(d|p)·a_p(C_1), from card_cd_affine_eq + sum_quadraticChar_twist),
  `coeff_twist_quadratic`, `jacobiSym_sq_of_not_dvd`, `eulerCoeff_twist` (all d, p prime, k),
  `cdCoeff_twist`: cdCoeff d n = J(d|n)·cdCoeff 1 n for every d and n ≠ 0 (formal identity of the Euler products).
- `twChar d` on (ZMod 4d)²: ¼·J(d | val² + val²)·unitOf(val mod 4); `unitG_eq_zero_of_two_mul` (decide),
  `twChar_intCast`: for q ∈ normFiber n, twChar d (q mod 4d) = ¼ J(d|n) unitOf(q mod 4) (periodicity of J(d|·) mod 4d on odd args).
- `isLContinuation_of_squarefree : GaussPointCount → Squarefree d → ∃ F, IsLContinuation (C_d) F`.
- **`ZInQ.Contrib.heckeContinuation_of_gaussPointCount : HeckeAll.GaussPointCount → ZInQ.Literature.HeckeContinuation`**
  (d = b²a, a squarefree, via LSeries_cd_sq_mul).
- HeckeFE.lean: verbatim copy of scratch/bp-hecke-fe/HeckeFE.lean, namespace BpHeckeFE → ZInQ.Contrib.HeckeAll
  (GaussPointCount unchanged). Built with lake (20 s).

## Checks
- (VERIFIED, PARI via cypari2, `twist_check.py` → `out_twist_check.txt`, 26 values of d) a_n(C_d) = J(d'|n)·a_n(C_1)
  for n ≤ 300, d' = squarefree part of d, d ∈ {1,2,3,5,6,7,10,11,13,14,15,21,22,30,34,4,8,9,12,18,20,25,27,45,50,72}:
  0 mismatches; no multiplicative reduction anywhere; for squarefree d PARI's global minimal model has u = 1
  (y² = x³ − d²x minimal at every p, matching `isMinimal_cdLocal'`); conductor 2^5 d² (d odd), 2^6 (d/2)²·… (d even:
  f₂ = 6, Kodaira code −6 = I₁*), f_p = 2 at odd p | d.
- (VERIFIED, `lake env lean scratch/hecke-all/ComposeTest.lean`, no errors) a GaussPointCount over independent
  verbatim copies of normFiber/unitOf/gz is accepted by `heckeContinuation_of_gaussPointCount` (definitional
  unfolding), so a proof of the gauss-proof task's copy composes directly.
- (VERIFIED, compiled; axioms standard) `ZInQ.Contrib.heckeContinuation_functionalEquation5_of_gaussPointCount :
  GaussPointCount → Literature.HeckeContinuation ∧ Literature.FunctionalEquation5`. Axiom check file:
  scratch/hecke-all/axioms.lean.

## Provider (after merging origin/wip/gauss-proof 912f839b)
- (VERIFIED, `lake env lean scratch/hecke-all/Provider.lean`, ~22:25; axioms propext, Classical.choice, Quot.sound)
  `theorem ZInQ.Contrib.heckeContinuation : ZInQ.Literature.HeckeContinuation :=
     heckeContinuation_of_gaussPointCount ZInQ.Contrib.GaussFE.gaussPointCount` (scratch file, since a
  HeckeAll module may not import GaussFE; type is exactly the hypothesis, no extra hypotheses).
