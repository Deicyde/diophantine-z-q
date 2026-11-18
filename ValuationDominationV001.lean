import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# A valuation subring dominated by another is equal to it

If `V ≤ W` are valuation subrings of a field and every nonunit of `V` is a nonunit of `W`
(`W` dominates `V`), then `V = W`: an element of `W \ V` has inverse a nonunit of `V`, hence of `W`,
which is impossible for the inverse of an element of `W`. This is the step identifying a valuation
ring of a finite extension with the localization of the integral closure at its center.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

variable {F : Type*} [Field F]

theorem valuationSubring_eq_of_le_of_nonunits_le {V W : ValuationSubring F} (hVW : V ≤ W)
    (hm : V.nonunits ≤ W.nonunits) : V = W := by
  refine le_antisymm hVW fun x hx => ?_
  by_contra hxV
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hnot : ¬ V.valuation x ≤ 1 := fun h => hxV ((V.valuation_le_one_iff x).1 h)
  have hinvV : x⁻¹ ∈ V.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff, Valuation.map_inv,
      inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hx0))]
    exact lt_of_not_ge hnot
  have hinvW := hm hinvV
  rw [ValuationSubring.mem_nonunits_iff, Valuation.map_inv,
    inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hx0))] at hinvW
  exact (not_le.mpr hinvW) ((W.valuation_le_one_iff x).2 hx)

end InertiaPointDescent
