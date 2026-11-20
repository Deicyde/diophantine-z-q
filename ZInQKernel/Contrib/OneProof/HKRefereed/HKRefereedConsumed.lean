import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-! # The portion of Kolyvagin's theorem used for pole completeness -/

namespace ZInQ.Manuscript.HKRefereed

/-- At the pole descent call, analytic rank one on the modular curve `E_ℓ` supplies an
infinite-order rational point. The eight-class assumption is already available at that call. -/
def HKConsumed : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (PoleRC.SelM ℓ).ncard = 8 →
    PoleS12.IsModular (curve (ℓ : ℚ)) → AnalyticRankOne (curve (ℓ : ℚ)) →
    ∃ P : (curve (ℓ : ℚ)).toAffine.Point, ¬ IsOfFinAddOrder P

/-- The headline's old hypothesis supplies the consumed fragment through its rank projection. -/
theorem hkConsumed_of_hK (hK : PoleS12.KolyvaginThm1) : HKConsumed := by
  intro ℓ hℓ _ _ _ hM hA
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  exact PoleRC.exists_not_isOfFinAddOrder_of_rank
    (hK _ (PoleRC.curve_isElliptic hℓ0) hM hA).1

end ZInQ.Manuscript.HKRefereed

#print axioms ZInQ.Manuscript.HKRefereed.hkConsumed_of_hK
