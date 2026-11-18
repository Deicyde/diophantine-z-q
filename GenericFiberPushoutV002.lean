import ExtendedRingMapsV003
import Mathlib.RingTheory.Localization.BaseChange

/-! # The actual generic fiber as a localization and algebraic pushout -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- Inverting any nonzero nonunit of a DVR gives its ambient fraction field. -/
theorem fraction_field_away_nonunit (w : ValuationSubring M) [IsDiscreteValuationRing w]
    (a : w) (ha0 : a ≠ 0) (ha : ¬ IsUnit a) : IsLocalization.Away a M := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w
  obtain ⟨e, u, hau⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
  have he : 1 ≤ e := by
    by_contra h
    have he0 : e = 0 := by omega
    exact ha (by simpa [hau, he0] using u.isUnit)
  apply IsLocalization.Away.mk a
  · exact isUnit_iff_ne_zero.2 (fun h => ha0 (Subtype.ext h))
  · intro x
    obtain ⟨c, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := w) x
    obtain ⟨n, v, hbv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, c * (v⁻¹ : wˣ) * (u : w) ^ n * π ^ ((e - 1) * n), ?_⟩
    rw [hau, hbv]
    change (c : M) / ((v : M) * (π : M) ^ n) * ((u : M) * (π : M) ^ e) ^ n =
      (c : M) * ((v⁻¹ : wˣ) : M) * (u : M) ^ n * (π : M) ^ ((e - 1) * n)
    have hπ0 : (π : M) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    have hv0 : (v : M) ≠ 0 := (Units.map w.subtype.toMonoidHom v).ne_zero
    have hvinv : ((v⁻¹ : wˣ) : M) = (v : M)⁻¹ := map_units_inv w.subtype v
    have hen : e * n = n + (e - 1) * n := by
      have he' : e = 1 + (e - 1) := by omega
      nth_rw 1 [he']
      rw [add_mul, one_mul]
    rw [hvinv, mul_pow, ← pow_mul, hen, pow_add]
    field_simp
  · intro c d h
    exact ⟨0, by simpa using (Subtype.ext h : c = d)⟩

/-- The ambient extension field is the actual generic-fiber pushout of the
extended valuation ring along the base fraction-field inclusion. -/
theorem finite_extension_generic_pushout [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    letI := extensionRingAlgebra O w hw
    letI := extensionField_tower (M := M) O
    letI := extensionRing_tower O w hw
    Algebra.IsPushout O w K M := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionRingAlgebra O w hw
  letI := extensionField_tower (M := M) O
  letI := extensionRing_tower O w hw
  letI := finite_extension_isDiscreteValuationRing O w hw
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  letI := fraction_field_away O hϖ
  have ha0 : baseHom O w hw ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (baseHom_injective O w hw (by simpa using h))
  have ha : ¬ IsUnit (baseHom O w hw ϖ) := fun h =>
    hϖ.not_isUnit (IsUnit.of_map (baseHom O w hw) ϖ h)
  letI := fraction_field_away_nonunit w (baseHom O w hw ϖ) ha0 ha
  haveI : IsLocalization (Algebra.algebraMapSubmonoid w (Submonoid.powers ϖ)) M := by
    rw [Algebra.algebraMapSubmonoid_powers]
    change IsLocalization.Away (baseHom O w hw ϖ) M
    infer_instance
  exact Algebra.isPushout_of_isLocalization (Submonoid.powers ϖ) K w M

end FiniteExtensionValuation
