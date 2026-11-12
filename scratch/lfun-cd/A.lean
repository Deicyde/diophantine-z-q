import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

namespace ZInQ.Literature

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

theorem vK_algebraMap_lt_one_iff (r : R) :
    vK (algebraMap R K r) < 1 ↔ r ∈ IsLocalRing.maximalIdeal R := by
  rw [valuation_of_algebraMap, intValuation_lt_one_iff_mem]; rfl

/-- An integral model whose discriminant is not in `m ^ 12` is minimal. -/
theorem isMinimal_baseChange_of_notMem (W : WeierstrassCurve R)
    (hΔ : W.Δ ∉ IsLocalRing.maximalIdeal R ^ 12) : IsMinimal R (W⁄K) := by
  have hI : IsIntegral R (W⁄K) := ⟨W, rfl⟩
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ, map_mul, map_pow]
  by_cases h : vK (↑C.u⁻¹ : K) ≤ 1
  · exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h)
  · exfalso
    replace h := not_le.mp h
    have hu : vK (C.u : K) < 1 := by
      have : (C.u : K) = (↑C.u⁻¹ : K)⁻¹ := by simp
      rw [this, map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
    obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
    rw [← hr, vK_algebraMap_lt_one_iff] at hu
    obtain ⟨δ, hδ⟩ := Δ_integral_of_isIntegral R (C • W⁄K)
    apply hΔ
    have key : algebraMap R K W.Δ = algebraMap R K (r ^ 12 * δ) := by
      rw [map_mul, map_pow, hr, hδ, variableChange_Δ, ← mul_assoc, ← mul_pow]
      simp [baseChange, map_Δ]
    rw [IsFractionRing.injective R K key]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hu 12)


theorem pow_twelve_eq_one {x : WithZero (Multiplicative ℤ)} (h : x ^ 12 = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h (pow_lt_one₀ zero_le hx (by norm_num)).ne
  · exact hx
  · exact absurd h (one_lt_pow₀ hx (by norm_num)).ne'

/-- Two minimal models differ by a change of variables with `v(u) = 1`. -/
theorem vK_u_eq_one {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    [hW : IsMinimal R W] [hCW : IsMinimal R (C • W)] : vK (C.u : K) = 1 := by
  have hI : IsIntegral R (C • W) := inferInstance
  have hI' : IsIntegral R W := inferInstance
  have h1 := hW.val_Δ_maximal.2 (j := C) hI
  have h2 := hCW.val_Δ_maximal.2 (j := C⁻¹) (by simpa using hI')
  simp only [one_smul, inv_smul_smul, ← Subtype.coe_le_coe,
    valuation_Δ_aux_eq_of_isIntegral] at h1 h2
  have hab : vK W.Δ = vK (C • W).Δ := by
    rcases le_total (vK W.Δ) (vK (C • W).Δ) with h | h
    · exact le_antisymm h (h1 h)
    · exact le_antisymm (h2 h) h
  rw [variableChange_Δ, map_mul, map_pow] at hab
  have ha : vK W.Δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hΔ
  have h12 : vK (↑C.u⁻¹ : K) ^ 12 = 1 := by
    have := mul_right_cancel₀ ha (hab.symm.trans (one_mul _).symm)
    exact this
  have h3 := pow_twelve_eq_one h12
  have : (C.u : K) = (↑C.u⁻¹ : K)⁻¹ := by simp
  rw [this, map_inv₀, h3, inv_one]

/-- A change of variables with `v(u) = 1` between minimal models descends to the reductions. -/
theorem exists_reduction_variableChange (W : WeierstrassCurve K) (C : VariableChange K)
    [IsMinimal R W] [IsMinimal R (C • W)] (hu : vK (C.u : K) = 1) :
    ∃ C' : VariableChange (IsLocalRing.ResidueField R),
      (C • W).reduction R = C' • W.reduction R := by
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
  have hr1 : IsUnit r := by
    rw [← hr, valuation_of_algebraMap, intValuation_eq_one_iff] at hu
    exact IsLocalRing.notMem_maximalIdeal.mp hu
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (W := W) (W' := C • W) rfl
    (u := hr1.unit) hr
  have hI : integralModel R (C • W) = CR • integralModel R W := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
    show (integralModel R (C • W)).map _ = (CR • integralModel R W).map _
    rw [← map_variableChange]
    change (integralModel R (C • W))⁄K = CR.baseChange K • (integralModel R W)⁄K
    rw [baseChange_integralModel_eq, baseChange_integralModel_eq, hCR]
  refine ⟨CR.map (IsLocalRing.residue R), ?_⟩
  simp only [reduction, hI, map_variableChange]

end Generic

section Points

variable {F : Type*} [Field F]

theorem equation_variableChange_iff (E : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • E).toAffine.Equation x y ↔
      E.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

/-- The affine solutions of `C • E` and of `E` correspond. -/
noncomputable def solutionsVariableChangeEquiv (E : WeierstrassCurve F) (C : VariableChange F) :
    {xy : F × F // (C • E).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // E.toAffine.Equation xy.1 xy.2} where
  toFun P := ⟨(C.u ^ 2 * P.1.1 + C.r, C.u ^ 3 * P.1.2 + C.s * C.u ^ 2 * P.1.1 + C.t),
    (equation_variableChange_iff E C _ _).mp P.2⟩
  invFun P := ⟨((P.1.1 - C.r) / C.u ^ 2, (P.1.2 - C.s * (P.1.1 - C.r) - C.t) / C.u ^ 3), by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rw [equation_variableChange_iff]
    convert P.2 using 1 <;> field_simp <;> ring⟩
  left_inv P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring
  right_inv P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring

/-- The points of an elliptic curve are the affine solutions and the point at infinity. -/
noncomputable def pointEquivOption (E : WeierstrassCurve F) [E.IsElliptic] :
    E.toAffine.Point ≃ Option {xy : F × F // E.toAffine.Equation xy.1 xy.2} :=
  (Equiv.subtypeUnivEquiv (p := fun _ : E.toAffine.Point => True) fun _ => trivial).symm.trans
    ((Affine.pointEquivSubtype (W' := E.toAffine) trivial).trans
      (Equiv.optionCongr (Equiv.subtypeEquivRight fun _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩)))

theorem natCard_point_variableChange (E : WeierstrassCurve F) [E.IsElliptic]
    (C : VariableChange F) :
    Nat.card (C • E).toAffine.Point = Nat.card E.toAffine.Point :=
  Nat.card_congr ((pointEquivOption _).trans
    ((Equiv.optionCongr (solutionsVariableChangeEquiv E C)).trans (pointEquivOption E).symm))

end Points

section LocalPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

theorem minimal_eq_smul (W : WeierstrassCurve K) :
    W.minimal R = (W.exists_isMinimal R).choose • W := rfl

theorem vK_minimal_Δ (W : WeierstrassCurve K) [IsMinimal R W] (hΔ : W.Δ ≠ 0) :
    vK (W.minimal R).Δ = vK W.Δ := by
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  rw [minimal_eq_smul, variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    vK_u_eq_one hΔ, inv_one, one_pow, one_mul]

theorem vK_minimal_c₄ (W : WeierstrassCurve K) [IsMinimal R W] (hΔ : W.Δ ≠ 0) :
    vK (W.minimal R).c₄ = vK W.c₄ := by
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  rw [minimal_eq_smul, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    vK_u_eq_one hΔ, inv_one, one_pow, one_mul]

open Polynomial in
/-- The local polynomial at a place of additive reduction of a minimal model is `1`. -/
theorem localPolynomial_of_hasAdditiveReduction (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    [h : HasAdditiveReduction R W] : W.localPolynomial R = 1 := by
  have hΔ' : vK (W.minimal R).Δ < 1 := by rw [vK_minimal_Δ W hΔ]; exact h.badReduction
  have hc' : vK (W.minimal R).c₄ < 1 := by rw [vK_minimal_c₄ W hΔ]; exact h.additiveReduction
  have h1 : ¬(W.minimal R).HasGoodReduction R := fun hg => hΔ'.ne hg.goodReduction
  have h2 : ¬(W.minimal R).HasSplitMultiplicativeReduction R := fun hs =>
    hc'.ne hs.toHasMultiplicativeReduction.multiplicativeReduction
  have h3 : ¬(W.minimal R).HasMultiplicativeReduction R := fun hm =>
    hc'.ne hm.multiplicativeReduction
  unfold localPolynomial
  rw [if_neg h1, if_neg h2, if_neg h3]

theorem natCard_point_reduction_minimal (W : WeierstrassCurve K) [h : HasGoodReduction R W] :
    Nat.card ((W.minimal R).reduction R).toAffine.Point = Nat.card (W.reduction R).toAffine.Point := by
  have hΔ : W.Δ ≠ 0 := fun h0 => by simpa [h0] using h.goodReduction
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  obtain ⟨C', hC'⟩ := exists_reduction_variableChange W _ (vK_u_eq_one hΔ (R := R)
    (W.exists_isMinimal R).choose)
  have : (W.reduction R).IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp h
  change Nat.card (((W.exists_isMinimal R).choose • W).reduction R).toAffine.Point = _
  rw [hC', natCard_point_variableChange]

open Polynomial in
/-- The local polynomial at a place of good reduction of a minimal model `W` is
`1 - a T + q T ^ 2` with `a = q + 1 - #W̃(κ)`, computed from `W` itself. -/
theorem localPolynomial_of_hasGoodReduction (W : WeierstrassCurve K)
    [h : HasGoodReduction R W] : W.localPolynomial R =
      1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
        Nat.card (W.reduction R).toAffine.Point) * X +
      C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  have hΔ : W.Δ ≠ 0 := fun h0 => by simpa [h0] using h.goodReduction
  have hg : (W.minimal R).HasGoodReduction R :=
    ⟨by rw [vK_minimal_Δ W hΔ]; exact h.goodReduction⟩
  unfold localPolynomial
  rw [if_pos hg, natCard_point_reduction_minimal]

end LocalPolynomial

end ZInQ.Literature
