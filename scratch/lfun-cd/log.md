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
