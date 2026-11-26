import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientRegularity

/-! # Reduction of the comparison to the marked cover -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open ModelGeneric ModelGeneric2

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The all-point specialization identity is equivalent to computing the quotient
on the actual marked cover. Every complex level point lifts to this cover. -/
theorem rationalQuotientCoordinate_specializes_iff_marked {n : ℕ} [NeZero (n + 2)]
    (h₂ : 2 ≤ n + 2) :
    (∀ x : Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ,
      x (rationalQuotientCoordinate h₂).val = pairQuotientJ (rationalPoints h₂ x)) ↔
    (∀ f : rationalCover (n + 2) →ₐ[ℚ] ℂ,
      let A := shortCoverPair rationalLevel_isUnit f
      f (Y0RationalInclusion h₂ (rationalQuotientCoordinate h₂).val) =
        A.equation.cyclicQuotientJ A.subgroup.val (n + 2)) := by
  have hread (f : rationalCover (n + 2) →ₐ[ℚ] ℂ) :
      rationalPoints h₂ (f.comp (Y0RationalInclusion h₂)) =
        Quot.mk _ (shortCoverPair rationalLevel_isUnit f) :=
    (rationalPointReading h₂).property f
  constructor
  · intro h f
    simpa only [AlgHom.comp_apply, hread, pairQuotientJ_mk] using
      h (f.comp (Y0RationalInclusion h₂))
  · intro h x
    obtain ⟨f, hf⟩ := shortCoverPairClass_surjective rationalLevel_isUnit
      (by norm_num) (by norm_num) (rationalPoints h₂ x)
    have hfx : f.comp (Y0RationalInclusion h₂) = x :=
      (rationalPoints h₂).injective ((hread f).trans hf)
    rw [← hfx, hread, pairQuotientJ_mk]
    exact h f

#print axioms rationalQuotientCoordinate_specializes_iff_marked

end WeierstrassCurve.ModelLevels.ModelGeneric3
