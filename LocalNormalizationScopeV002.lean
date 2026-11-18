import ExtendedPresentationV002

/-! # Distinguishing the selected local ring from the whole normalization -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The selected valuation ring equals the whole normalization precisely when
it is integral over the base. This does not assume that integrality holds. -/
theorem extended_integral_iff_normalization_eq (O : ValuationSubring K)
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    letI := extensionRingAlgebra O w hw
    Algebra.IsIntegral O w ↔ (integralClosure O M).toSubring = w.toSubring := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionRingAlgebra O w hw
  letI := extensionRing_tower O w hw
  constructor
  · intro h
    letI := h
    apply le_antisymm (normalization_le O w hw)
    intro x hx
    exact (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : w)).map (IsScalarTower.toAlgHom O w M)
  · intro h
    constructor
    intro x
    have hx : IsIntegral O (x : M) := by
      change (x : M) ∈ (integralClosure O M).toSubring
      rw [h]
      exact x.2
    exact IsIntegral.tower_bot (ValuationSubring.subtype_injective w) hx

/-- In the finite separable case, module-finiteness of the selected valuation
ring is equivalent to integrality. It is not an automatic consequence of finiteness
of the field extension. -/
theorem finite_separable_extended_finite_iff_integral [FiniteDimensional K M]
    [Algebra.IsSeparable K M] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O) :
    letI := extensionRingAlgebra O w hw
    Module.Finite O w ↔ Algebra.IsIntegral O w := by
  letI := extensionRingAlgebra O w hw
  haveI : Algebra.FinitePresentation O w := finite_separable_extended_finitePresentation O w hw
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Algebra.IsIntegral.finite

end FiniteExtensionValuation
