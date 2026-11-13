import ZInQKernel.Contrib.HeckeAll.LocalCd

/-!
# Mathlib's L-function is invariant under a change of variables (integral `j`)

Mathlib's `WeierstrassCurve.LFunction` is built from the local polynomials of a minimal model
chosen by `Classical.choice`. We show that it does not change under a change of variables over
`ℚ` when the `j`-invariant is integral at every place (`v(c₄³) ≤ v(Δ)`), which excludes
multiplicative reduction. Consequence: `L(C_{m² d}, s) = L(C_d, s)` (`LFunction_cd_sq_mul`),
since `(x, y) ↦ (x / m², y / m³)` maps `C_{m² d}` to `C_d`.
-/

namespace ZInQ.Contrib.HeckeAll

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum ZInQ.Literature

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

/-- Integral `j` excludes multiplicative reduction of every model. -/
theorem not_hasMultiplicativeReduction_smul (W : WeierstrassCurve K)
    (hj : vK W.c₄ ^ 3 ≤ vK W.Δ) (C : VariableChange K) :
    ¬ (C • W).HasMultiplicativeReduction R := by
  intro h
  have h1 := h.badReduction
  have h2 := h.multiplicativeReduction
  rw [variableChange_Δ, map_mul, map_pow] at h1
  rw [variableChange_c₄, map_mul, map_pow] at h2
  have h3 : vK (↑C.u⁻¹ : K) ^ 12 * vK W.c₄ ^ 3 = 1 := by
    calc vK (↑C.u⁻¹ : K) ^ 12 * vK W.c₄ ^ 3 = (vK (↑C.u⁻¹ : K) ^ 4 * vK W.c₄) ^ 3 := by
          rw [mul_pow, ← pow_mul]
      _ = 1 := by rw [h2, one_pow]
  have h4 : vK (↑C.u⁻¹ : K) ^ 12 * vK W.c₄ ^ 3 ≤ vK (↑C.u⁻¹ : K) ^ 12 * vK W.Δ :=
    mul_le_mul_right hj _
  rw [h3] at h4
  exact absurd (lt_of_le_of_lt h4 h1) (lt_irrefl 1)

theorem hj_smul (W : WeierstrassCurve K) (hj : vK W.c₄ ^ 3 ≤ vK W.Δ) (C : VariableChange K) :
    vK (C • W).c₄ ^ 3 ≤ vK (C • W).Δ := by
  rw [variableChange_c₄, variableChange_Δ, map_mul, map_mul, map_pow, map_pow, mul_pow,
    ← pow_mul]
  exact mul_le_mul_right hj _

open Polynomial Classical in
/-- With integral `j`, the local polynomial is the good-reduction polynomial or `1`. -/
theorem localPolynomial_eq_ite (X : WeierstrassCurve K) (hj : vK X.c₄ ^ 3 ≤ vK X.Δ) :
    X.localPolynomial R = if (X.minimal R).HasGoodReduction R then
      1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
        Nat.card ((X.minimal R).reduction R).toAffine.Point) * Polynomial.X +
      C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * Polynomial.X ^ 2 else 1 := by
  have hm : ¬ (X.minimal R).HasMultiplicativeReduction R :=
    not_hasMultiplicativeReduction_smul X hj _
  have hs : ¬ (X.minimal R).HasSplitMultiplicativeReduction R := fun h =>
    hm h.toHasMultiplicativeReduction
  unfold localPolynomial
  simp only [hm, hs, ↓reduceIte]

theorem natCard_reduction_congr {M N : WeierstrassCurve K} (h : M = N) [IsMinimal R M]
    [IsMinimal R N] :
    Nat.card (M.reduction R).toAffine.Point = Nat.card (N.reduction R).toAffine.Point := by
  subst h; exact rfl

open Classical in
/-- **Invariance of the local polynomial** under a change of variables, for integral `j`. -/
theorem localPolynomial_smul (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    (hj : vK W.c₄ ^ 3 ≤ vK W.Δ) (C : VariableChange K) :
    (C • W).localPolynomial R = W.localPolynomial R := by
  rw [localPolynomial_eq_ite (C • W) (hj_smul W hj C), localPolynomial_eq_ite W hj]
  set C0 := (W.exists_isMinimal R).choose with hC0
  set C1 := ((C • W).exists_isMinimal R).choose with hC1
  set D := (C1 * C) * C0⁻¹ with hD
  have hA : W.minimal R = C0 • W := rfl
  have hB : (C • W).minimal R = D • (W.minimal R) := by
    rw [hA, hD, mul_smul, inv_smul_smul, mul_smul]; rfl
  have hAΔ : (W.minimal R).Δ ≠ 0 := by
    rw [hA, variableChange_Δ]; exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hΔ
  have : IsMinimal R (D • W.minimal R) := hB ▸ inferInstance
  have hu : vK (D.u : K) = 1 := vK_u_eq_one hAΔ D
  have hvΔ : vK ((C • W).minimal R).Δ = vK (W.minimal R).Δ := by
    rw [hB, variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one,
      one_pow, one_mul]
  have hgood : ((C • W).minimal R).HasGoodReduction R ↔ (W.minimal R).HasGoodReduction R := by
    rw [hasGoodReduction_iff, hasGoodReduction_iff, hvΔ]
    exact ⟨fun h => ⟨inferInstance, h.2⟩, fun h => ⟨inferInstance, h.2⟩⟩
  by_cases hg : (W.minimal R).HasGoodReduction R
  · simp only [hgood.mpr hg, hg, ↓reduceIte]
    have hE : ((W.minimal R).reduction R).IsElliptic :=
      (hasGoodReduction_iff_isElliptic_reduction R).mp hg
    obtain ⟨C', hC'⟩ := exists_reduction_variableChange (W.minimal R) D hu
    rw [natCard_reduction_congr (R := R) hB, hC', natCard_point_variableChange]
  · simp only [hgood, hg, ↓reduceIte]

end Generic

section Global

open Rat.HeightOneSpectrum

/-- The local `j`-integrality of `C_d`: `c₄³ = 1728 Δ`. -/
theorem hj_cdLocal (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (d : ℕ) :
    valuation (v.adicCompletion ℚ) (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) (cdLocal v d).c₄ ^ 3 ≤
    valuation (v.adicCompletion ℚ) (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) (cdLocal v d).Δ := by
  have h : (cdLocal v d).c₄ ^ 3 = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (1728 : v.adicCompletionIntegers ℚ) * (cdLocal v d).Δ := by
    rw [cdLocal_c₄_eq, cdLocal_Δ_eq, ← map_pow, ← map_mul]
    congr 1; push_cast; ring
  rw [← map_pow, h, map_mul, valuation_of_algebraMap]
  exact mul_le_of_le_one_left zero_le (intValuation_le_one _ _)

/-- The change of variables `(x, y) ↦ (x / m², y / m³)`. -/
noncomputable def scaleChange (m : ℕ) (hm : m ≠ 0) : VariableChange ℚ :=
  ⟨Units.mk0 (m : ℚ) (Nat.cast_ne_zero.mpr hm), 0, 0, 0⟩

theorem scaleChange_smul (d m : ℕ) (hm : m ≠ 0) :
    scaleChange m hm • shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2) = shortCurve (-(d : ℚ) ^ 2) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  ext <;> simp [scaleChange, variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, shortCurve]
  field_simp

/-- **`L(C_{m² d}, s) = L(C_d, s)`** (Mathlib's L-function is an isomorphism invariant). -/
theorem LFunction_cd_sq_mul (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) :
    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LFunction = (shortCurve (-(d : ℚ) ^ 2)).LFunction := by
  rw [← scaleChange_smul d m hm]
  unfold LFunction
  congr 1
  funext v
  have hloc : ((scaleChange m hm • shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).baseChange
      (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      (cdLocal v (m ^ 2 * d)).localPolynomial (v.adicCompletionIntegers ℚ) := by
    rw [cdLocal, baseChange, ← map_variableChange]
    exact localPolynomial_smul _ (cdLocal_Δ_ne_zero v (by positivity)) (hj_cdLocal v _) _
  unfold localEulerFactor localPowerSeries
  rw [hloc]

theorem LSeries_cd_sq_mul (d m : ℕ) (hd : d ≠ 0) (hm : m ≠ 0) (s : ℂ) :
    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LSeries s = (shortCurve (-(d : ℚ) ^ 2)).LSeries s := by
  simp only [WeierstrassCurve.LSeries, LFunction_cd_sq_mul d m hd hm]

end Global

end ZInQ.Contrib.HeckeAll
