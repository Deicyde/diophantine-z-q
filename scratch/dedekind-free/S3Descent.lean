import ZInQKernel.Contrib.OneProof.NeronGoodModelIso

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace DedekindFree

section Descent

variable {S S' : Scheme.{0}} (p : S' ⟶ S) [Flat p] [Surjective p] [QuasiCompact p]

instance effEpi_fst (X : Over S) : EffectiveEpi (pullback.fst X.hom p) := inferInstance

/-- Base change along a faithfully flat quasi-compact `p` is injective on morphisms. -/
theorem map_injective (X Y : Over S) :
    Function.Injective (fun f : X ⟶ Y => (Over.pullback p).map f) := by
  intro f g h
  simp only at h
  have e1 : ((Over.pullback p).map f).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left := by simp
  have e2 : ((Over.pullback p).map g).left ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ g.left := by simp
  ext1
  rw [← cancel_epi (pullback.fst X.hom p), ← e1, ← e2, h]

/-- **Descent of morphisms along a faithfully flat quasi-compact `p`** (Stacks 023Q, Mathlib's `EffectiveEpi`). -/
theorem descend (X Y : Over S) (b : (Over.pullback p).obj X ⟶ (Over.pullback p).obj Y)
    (hb : ∀ (W : Scheme.{0}) (a₁ a₂ : W ⟶ ((Over.pullback p).obj X).left),
      a₁ ≫ pullback.fst X.hom p = a₂ ≫ pullback.fst X.hom p →
        a₁ ≫ b.left ≫ pullback.fst Y.hom p = a₂ ≫ b.left ≫ pullback.fst Y.hom p) :
    ∃ f : X ⟶ Y, (Over.pullback p).map f = b := by
  let fl : X.left ⟶ Y.left :=
    EffectiveEpi.desc (pullback.fst X.hom p) (b.left ≫ pullback.fst Y.hom p) (fun a₁ a₂ h => hb _ a₁ a₂ h)
  have hfl : pullback.fst X.hom p ≫ fl = b.left ≫ pullback.fst Y.hom p := EffectiveEpi.fac _ _ _
  have hw : fl ≫ Y.hom = X.hom := by
    have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    rw [← cancel_epi (pullback.fst X.hom p), reassoc_of% hfl, pullback.condition,
      ← Category.assoc, this, pullback.condition]
  refine ⟨Over.homMk fl hw, ?_⟩
  ext1
  apply pullback.hom_ext
  · simp [hfl]
  · have := Over.w b
    simp only [Over.pullback_obj_hom] at this
    simp [this]

end Descent

end DedekindFree
