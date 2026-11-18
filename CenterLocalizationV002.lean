import ValuationLocalizationV006

/-! # The localization class of the actual selected valuation ring -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {F : Type*} [Field F]

/-- The fraction description constructs the localization class for the literal
inclusion, rather than merely an abstract isomorphic ring. -/
theorem dedekind_center_isLocalization (C : Subring F) [IsDedekindDomain C]
    [IsFractionRing C F] (w : ValuationSubring F) (hC : C ≤ w.toSubring)
    (hw : w ≠ ⊤)
    (hq0 : (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC) ≠ ⊥) :
    letI := (Subring.inclusion hC).toAlgebra
    IsLocalization.AtPrime w ((IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)) := by
  letI := (Subring.inclusion hC).toAlgebra
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  have hdesc := dedekind_center_fraction_description C w hC hw hq0
  refine ⟨?_, ?_, ?_⟩
  · intro s
    change IsUnit (Subring.inclusion hC s)
    have hs : (s : C) ∉ q := s.2
    simpa only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] using hs
  · intro z
    obtain ⟨a, s, hs, hz⟩ := (hdesc (z : F)).1 z.2
    refine ⟨⟨a, ⟨s, hs⟩⟩, ?_⟩
    apply Subtype.ext
    change (z : F) * (s : F) = (a : F)
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      have : s = 0 := Subtype.ext h0
      exact hs (this ▸ Ideal.zero_mem q)
    rw [hz, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  · intro a b h
    refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, one_mul] using
      (Subtype.ext (congrArg (fun z : w => (z : F)) h) : a = b)

end FiniteExtensionValuation
