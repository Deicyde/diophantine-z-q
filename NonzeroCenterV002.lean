import ValuationLocalizationV006

/-! # Nonzero centers of nontrivial valuation rings in a fraction field -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {F : Type*} [Field F]

/-- If a subring has the ambient field as fraction field, a nontrivial valuation
ring containing it has a nonzero center. No dimension or Noetherian premise is needed. -/
theorem center_ne_bot_of_ne_top (C : Subring F) [IsFractionRing C F]
    (w : ValuationSubring F) (hC : C ≤ w.toSubring) (hw : w ≠ ⊤) :
    (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC) ≠ ⊥ := by
  let q : Ideal C := (IsLocalRing.maximalIdeal w).comap (Subring.inclusion hC)
  intro hq
  have hunit : ∀ a : C, a ≠ 0 → IsUnit (Subring.inclusion hC a) := by
    intro a ha
    by_contra hnu
    have hqa : a ∈ q := by
      simpa only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnu
    have ha0 : a = 0 := by simpa only [q, hq, Ideal.mem_bot] using hqa
    exact ha ha0
  have hall : ∀ x : F, x ∈ w := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := C) x
    have hu := hunit b (nonZeroDivisors.ne_zero hb)
    have hv : w.valuation (b : F) = 1 := (w.valuation_eq_one_iff _).1 hu
    have hi : (b : F)⁻¹ ∈ w := (w.valuation_le_one_iff _).1 (by rw [map_inv₀, hv, inv_one])
    change (a : F) / (b : F) ∈ w
    rw [div_eq_mul_inv]
    exact w.mul_mem _ _ (hC a.2) hi
  exact hw (ValuationSubring.ext w ⊤ fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => hall x⟩)

end FiniteExtensionValuation
