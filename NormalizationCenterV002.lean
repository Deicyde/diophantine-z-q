import NormalizationCoreV002
import ValuationLocalizationV006

/-! # The actual center of the selected finite-extension valuation ring -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The extended valuation is genuinely nontrivial because the base is a DVR. -/
theorem extended_ne_top (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) : w ≠ ⊤ := by
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hc0 : algebraMap K M (a : K) ≠ 0 :=
    (map_ne_zero _).2 (fun h => ha.ne_zero (Subtype.ext h))
  intro h
  have hi : (algebraMap K M (a : K))⁻¹ ∈ w := h ▸ ValuationSubring.mem_top _
  have hle : 1 ≤ w.valuation (algebraMap K M (a : K)) :=
    (w.valuation.one_le_val_iff hc0).2 ((w.valuation_le_one_iff _).2 hi)
  exact not_le_of_gt (base_uniformizer_value O w hw ha).2 hle

/-- The actual valuation ring in a finite separable extension consists exactly
of fractions in the normalization with denominator outside its nonzero center. -/
theorem finite_separable_center_description [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    ∃ hC : (integralClosure O M).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧ ∀ x : M, x ∈ w ↔ ∃ a s : (integralClosure O M),
        s ∉ q ∧ x = (a : M) * (s : M)⁻¹ := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionField_tower (M := M) O
  let C := integralClosure O M
  have hC : C.toSubring ≤ w.toSubring := normalization_le O w hw
  haveI : IsDedekindDomain C := (finite_separable_normalization (M := M) O).2.2.1
  haveI : IsFractionRing C M := (finite_separable_normalization (M := M) O).2.2.2
  haveI : IsDedekindDomain C.toSubring := inferInstanceAs (IsDedekindDomain C)
  haveI : IsFractionRing C.toSubring M := inferInstanceAs (IsFractionRing C M)
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hq0 : q ≠ ⊥ := by
    apply (Submodule.ne_bot_iff q).2
    refine ⟨algebraMap O C a, ?_, ?_⟩
    · change Subring.inclusion hC (algebraMap O C a) ∈ IsLocalRing.maximalIdeal w
      apply (w.valuation_lt_one_iff _).2
      exact (base_uniformizer_value O w hw ha).2
    · intro h0
      have hm : algebraMap K M (a : K) = 0 := congrArg (algebraMap C M) h0
      exact ha.ne_zero (Subtype.ext ((algebraMap K M).injective (by simpa using hm)))
  refine ⟨hC, hq0, ?_⟩
  exact dedekind_center_fraction_description C.toSubring w hC (extended_ne_top O w hw) hq0

/-- The original number-field case has the same selected-localization description. -/
theorem numberField_center_description [NumberField K] [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    ∃ hC : (integralClosure O M).toSubring ≤ w.toSubring,
      let q := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
      q ≠ ⊥ ∧ ∀ x : M, x ∈ w ↔ ∃ a s : (integralClosure O M),
        s ∉ q ∧ x = (a : M) * (s : M)⁻¹ := finite_separable_center_description O w hw

end FiniteExtensionValuation
