import ZInQKernel.Contrib.CloudR2Poincare.L3.B2KernelBundle

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {k : Type u} [Field k] (B : PkgI3.AbVar k)

/-- The rational b×B restriction is a genuine Cartesian fibre square. -/
theorem isPullback_firstSlice (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) :
    IsPullback (firstSlice B b).left B.X.hom (fst B.X B.X).left b.left := by
  haveI : IsIso (𝟙_ (Over (Spec (.of k)))).hom := by
    change IsIso (𝟙 (Spec (.of k)))
    infer_instance
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback B.X.hom B.X.hom).flip
  · have H : (firstSlice B b).left ≫ (snd B.X B.X).left = 𝟙 B.X.left := by
      rw [← Over.comp_left]
      simp [firstSlice]
    change IsPullback ((firstSlice B b).left ≫ (snd B.X B.X).left) B.X.hom B.X.hom
      (b.left ≫ B.X.hom)
    rw [H, Over.w b]
    change IsPullback (𝟙 B.X.left) B.X.hom B.X.hom (𝟙 (Spec (.of k)))
    exact IsPullback.id_horiz B.X.hom
  · rw [← Over.comp_left]
    simp [firstSlice]

/-- The rational B×b restriction is a genuine Cartesian fibre square. -/
theorem isPullback_secondSlice (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) :
    IsPullback (secondSlice B b).left B.X.hom (snd B.X B.X).left b.left := by
  haveI : IsIso (𝟙_ (Over (Spec (.of k)))).hom := by
    change IsIso (𝟙 (Spec (.of k)))
    infer_instance
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback B.X.hom B.X.hom)
  · have H : (secondSlice B b).left ≫ (fst B.X B.X).left = 𝟙 B.X.left := by
      rw [← Over.comp_left]
      simp [secondSlice]
    change IsPullback ((secondSlice B b).left ≫ (fst B.X B.X).left) B.X.hom B.X.hom
      (b.left ≫ B.X.hom)
    rw [H, Over.w b]
    change IsPullback (𝟙 B.X.left) B.X.hom B.X.hom (𝟙 (Spec (.of k)))
    exact IsPullback.id_horiz B.X.hom
  · rw [← Over.comp_left]
    simp [secondSlice]

end ZInQ.Contrib.CloudR2Poincare.L3
