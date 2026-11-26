import ZInQKernel.Contrib.OneProof.RankModelTangent
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.RouteK.Rank.LFunctionCd

/-! Weierstrass-model invariance for the actual Hasse–Weil series, including
both split and nonsplit multiplicative reduction. The generic minimal-model
lemmas in `LFunctionCd` apply here to every nonsingular equation, not just to
congruent-number curves. -/

namespace ZInQ.Manuscript.RankModel

open Polynomial WeierstrassCurve IsDedekindDomain.HeightOneSpectrum

section Local

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- On two minimal equations related by a change of coordinates, the
reduction data used by the local polynomial are identical. -/
private theorem localData_of_minimal_change (W : WeierstrassCurve K) (U : VariableChange K)
    [IsMinimal R W] [IsMinimal R (U • W)] (hΔ : W.Δ ≠ 0) :
    (HasGoodReduction R (U • W) ↔ HasGoodReduction R W) ∧
    (HasSplitMultiplicativeReduction R (U • W) ↔ HasSplitMultiplicativeReduction R W) ∧
    (HasMultiplicativeReduction R (U • W) ↔ HasMultiplicativeReduction R W) ∧
    Nat.card ((U • W).reduction R).toAffine.Point = Nat.card (W.reduction R).toAffine.Point := by
  have hu := ZInQ.Literature.vK_u_eq_one (R := R) hΔ U
  let v := valuation K (IsDiscreteValuationRing.maximalIdeal R)
  have hd : v (U • W).Δ = v W.Δ := by
    dsimp only [v]
    rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
      hu, inv_one, one_pow, one_mul]
  have hc : v (U • W).c₄ = v W.c₄ := by
    dsimp only [v]
    rw [variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
      hu, inv_one, one_pow, one_mul]
  have hg : HasGoodReduction R (U • W) ↔ HasGoodReduction R W := by
    rw [hasGoodReduction_iff, hasGoodReduction_iff]
    simp only [and_iff_right (show IsMinimal R (U • W) from inferInstance),
      and_iff_right (show IsMinimal R W from inferInstance)]
    exact congrArg (· = 1) hd |>.to_iff
  have hm : HasMultiplicativeReduction R (U • W) ↔ HasMultiplicativeReduction R W := by
    rw [hasMultiplicativeReduction_iff, hasMultiplicativeReduction_iff]
    simp only [and_iff_right (show IsMinimal R (U • W) from inferInstance),
      and_iff_right (show IsMinimal R W from inferInstance)]
    change (v (U • W).Δ < 1 ∧ v (U • W).c₄ = 1) ↔ (v W.Δ < 1 ∧ v W.c₄ = 1)
    rw [hd, hc]
  have hred := ZInQ.Literature.exists_reduction_variableChange W U hu
  refine ⟨hg, ?_, hm, ?_⟩
  · rw [hasSplitMultiplicativeReduction_iff_residue, hasSplitMultiplicativeReduction_iff_residue,
      hm, residueSplit_iff_of_variableChange hred]
  · obtain ⟨D, hD⟩ := hred
    rw [hD]
    exact Nat.card_congr (Affine.Point.equivVariableChange (W.reduction R) D)

/-- Reduction agrees when two equal minimal equations carry different proofs of minimality. -/
private theorem reduction_congr {W W' : WeierstrassCurve K} [IsMinimal R W] [IsMinimal R W']
    (h : W = W') : W.reduction R = W'.reduction R := by
  subst W'
  rfl

/-- The local factor is unchanged for every integral or nonintegral model
obtained by a variable change: their chosen minimal models are compared. -/
theorem localPolynomial_variableChange (W : WeierstrassCurve K) (U : VariableChange K)
    (hΔ : W.Δ ≠ 0) : (U • W).localPolynomial R = W.localPolynomial R := by
  let A := (W.exists_isMinimal R).choose
  let B := ((U • W).exists_isMinimal R).choose
  let D := B * U * A⁻¹
  have hA : W.minimal R = A • W := rfl
  have hB : (U • W).minimal R = B • (U • W) := rfl
  have hD : D • W.minimal R = (U • W).minimal R := by
    rw [hA, hB, show D = B * U * A⁻¹ by rfl, mul_smul, inv_smul_smul, mul_smul]
  let : IsMinimal R (D • W.minimal R) := hD ▸ inferInstance
  have hΔA : (W.minimal R).Δ ≠ 0 := by
    rw [hA, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero A.u⁻¹)) hΔ
  obtain ⟨hg, hs, hm, hcnt⟩ := localData_of_minimal_change (R := R) (W.minimal R) D hΔA
  rw [hD] at hg hs hm
  have hR := reduction_congr (R := R) hD
  rw [hR] at hcnt
  classical
  unfold localPolynomial
  simp only [hg, hs, hm, hcnt]

end Local

/-- The formal Dirichlet coefficients of the actual Mathlib L-function are
unchanged under an admissible change of rational Weierstrass coordinates. -/
theorem LFunction_variableChange (W : WeierstrassCurve ℚ) (U : VariableChange ℚ)
    (hΔ : W.Δ ≠ 0) : (U • W).LFunction = W.LFunction := by
  unfold LFunction
  congr 1
  funext p
  let L := p.adicCompletion ℚ
  let R := p.adicCompletionIntegers ℚ
  have hD : (W.baseChange L).Δ ≠ 0 := by
    change (W.map (algebraMap ℚ L)).Δ ≠ 0
    rw [map_Δ]
    exact fun h => hΔ ((algebraMap ℚ L).injective (h.trans (map_zero _).symm))
  have he : (U • W).baseChange L = U.baseChange L • W.baseChange L :=
    (map_variableChange W U (algebraMap ℚ L)).symm
  rw [he, localEulerFactor, localEulerFactor, localPowerSeries, localPowerSeries,
    localPolynomial_variableChange (R := R) (W.baseChange L) (U.baseChange L) hD]

/-- The complex L-series, not just its value at the central point, agrees
on rationally isomorphic Weierstrass models. -/
theorem LSeries_variableChange (W : WeierstrassCurve ℚ) (U : VariableChange ℚ)
    (hΔ : W.Δ ≠ 0) : (U • W).LSeries = W.LSeries := by
  funext s
  simp only [WeierstrassCurve.LSeries, LFunction_variableChange W U hΔ]

/-- Mordell–Weil rank is preserved by the actual additive point isomorphism. -/
theorem rank_variableChange (W : WeierstrassCurve ℚ) (U : VariableChange ℚ) :
    Module.rank ℤ (U • W).toAffine.Point = Module.rank ℤ W.toAffine.Point :=
  (Affine.Point.addEquivVariableChange W U).toIntLinearEquiv.rank_eq

end ZInQ.Manuscript.RankModel
