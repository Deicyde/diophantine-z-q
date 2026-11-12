# lfun-cd results log

## Step 0 (plan)
Mathlib API found (v4.35.0):
- `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v : v.adicCompletionIntegers ℚ ≃A[ℤ] ℤ_[primesEquiv v]`
  and `PadicInt.residueField : ResidueField ℤ_[p] ≃+* ZMod p` give the residue field of the completion.
- `IsDiscreteValuationRing.exists_lift_of_le_one`, `intValuation_le_pow_iff_mem`,
  `variableChange_integral_of_u_integral` (Reduction.lean), `map_variableChange`,
  `pointEquivSubtype` (points of an elliptic curve ≃ WithZero of solutions).
- `ArithmeticFunction.tendsTo_eulerProduct_ofPowerSeries` (needs `Northcott q`).
Plan: (A) generic DVR lemmas: Δ_R ∉ m^12 ⇒ minimal; two minimal models differ by a unit u, so
reduction type and #points of the reduction agree, so `localPolynomial` is computed from any
minimal model. (B) the curves C_d at R_v = completion of 𝓞ℚ at v. (C) Euler product coefficient
at a prime.

## Step 1 (local, done in scratch/lfun-cd/A.lean, compiles, no sorry)
- Generic DVR: `isMinimal_baseChange_of_notMem` (integral model with Δ ∉ m^12 is minimal);
  `vK_u_eq_one` (two minimal models differ by v(u)=1); `exists_reduction_variableChange`
  (such a change descends to the residue field, via Mathlib's `variableChange_integral_of_u_integral`);
  `natCard_point_variableChange`, `natCard_point_map_ringEquiv`;
  `localPolynomial_of_hasAdditiveReduction` (= 1) and `localPolynomial_of_hasGoodReduction`
  (= 1 - aT + qT², a from the given minimal model, not Mathlib's chosen one).
- Completion of 𝓞ℚ at v (p = natGenerator v): units / m^k membership of integers, residue field
  ≃ ZMod p, card = p (via `padicIntEquiv` and `PadicInt.residueField`).
- C_d: `isMinimal_cdLocal` (odd squarefree d, all v), `hasGoodReduction_cdLocal` (p ∤ 2d),
  `hasAdditiveReduction_cdLocal` (p | 2d), `localPolynomial_cdLocal_of_not_dvd`
  (1 - (p+1-#C_d(𝔽_p)) T + p T²), `localPolynomial_cdLocal_of_dvd` (= 1).

## Step 2 (global coefficients) and integration
- `LFunction_cd_apply_prime_pow` (coefficient at p^k = [T^k] 1/cdEulerPoly d p), via
  `tendsTo_eulerProduct_ofPowerSeries` with a `Northcott` instance for v ↦ #κ_v = natGenerator v,
  and the vanishing of the other factors at nontrivial divisors of p^k.
- `LFunction_cd_apply_prime` (a_p = p+1-#C_d(𝔽_p) for p ∤ 2d, 0 for p | 2d),
  `LFunction_cd_apply_prime_eq_sub_card` (a_p = p - #{y² = x³ - d²x over 𝔽_p}),
  `isMultiplicative_LFunction` (any W/ℚ), `LFunction_cd_apply` (all n ≠ 0),
  `LSeries_cd_eq` / `LSeries_cd_eq_of_mod_eight` (E.LSeries = LSeries of `cdCoeff d`).
- Final file ZInQKernel/RouteK/Rank/LFunctionCd.lean (scratch draft removed), imported from
  ZInQKernel.lean; 11 `#print axioms` lines added.
- `lake build ZInQKernel`: Build completed successfully (9923 jobs).
- `lake env lean scripts/print_axioms.lean`: 80 entries, all [propext, Classical.choice,
  Quot.sound] (output in scratch/lfun-cd/print_axioms.out).
