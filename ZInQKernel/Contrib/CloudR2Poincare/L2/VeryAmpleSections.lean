import ZInQKernel.Contrib.CloudR2Poincare.L2.LineBundleNonzero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

/-!
# Nonzero sections and trivial very ample bundles

This is the native properness/very-ampleness contradiction used in Mumford §6.
The coordinate sections are actual pulled-back O(1) sections. If the bundle is
trivial, they become global functions; over a proper integral scheme these form
a field. A nonzero coordinate is a unit, so its affine coordinate open is the
whole scheme. Proper and affine then gives a finite zero-dimensional scheme.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open Scheme.Modules ProjectiveSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- A free generator on a nonempty open cannot be zero. -/
theorem freeGenerator_ne_zero {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (hne : (U : Set X).Nonempty) {M : X.Modules}
    (s : Γ(M, U)) (hs : IsFreeGenerator s) : s ≠ 0 := by
  letI : Nonempty U := hne.to_subtype
  have : Nontrivial Γ(X, U) := inferInstance
  intro h
  have hi := (hs U le_rfl).1
  have heq : (1 : Γ(X, U)) = 0 := hi (by rw [h]; simp)
  exact one_ne_zero heq

/-- A very ample line bundle has a nonzero global section, stated as an
actual nonzero map from O_X. -/
theorem VeryAmple.exists_nonzero_unit_map {X S : Scheme.{u}} [IsIntegral X]
    {p : X ⟶ S} {M : X.Modules} (hM : VeryAmple p M) :
    ∃ s : unit X ⟶ M, s ≠ 0 := by
  obtain ⟨coordinates, hfinite, e, he, hp, ⟨comparison⟩⟩ := hM
  let N := twistRestrict e 1
  let u : coordinates → Γ(N, ⊤) := fun i => pullbackΓ e (twist coordinates S 1)
    (twistOneSection coordinates S i)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen coordinates S).symm ▸
      (show e x ∈ (⊤ : ℙ(coordinates; S).Opens) from trivial))
  let U := e ⁻¹ᵁ standardOpen coordinates S i
  have hne : (U : Set X).Nonempty := ⟨x, hi⟩
  have hgen : IsFreeGenerator (N.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (u i)) := by
    convert isFreeGenerator_pullbackSection_twistOneSection e i using 1 <;>
      simp only [N, U, twistRestrict, standardOpen, u, pullbackΓ_def, pullbackSection] <;> rfl
  have hu : u i ≠ 0 := by
    intro hz
    exact freeGenerator_ne_zero U hne _ hgen (by rw [hz, map_zero])
  refine ⟨homOfGlobalSection N (u i) ≫ comparison.inv, ?_⟩
  intro hs
  apply hu
  have hh : homOfGlobalSection N (u i) = 0 := by
    apply (cancel_mono comparison.inv).mp
    simpa only [zero_comp] using hs
  have hs' : (unitHomAddEquiv N) (homOfGlobalSection N (u i)) = 0 := by
    rw [hh, map_zero]
  simpa only [← unitHomAddEquiv_symm_apply, AddEquiv.apply_symm_apply] using hs'

/-- The basic open of a relative coordinate ratio is the intersection of the
two standard opens. This uses the native homogeneous-chart ratio formula. -/
theorem basicOpen_coordRatio (coordinates : Type u) (S : Scheme.{u}) (i j : coordinates) :
    ℙ(coordinates; S).basicOpen (coordRatio coordinates S i j) =
      standardOpen coordinates S i ⊓ standardOpen coordinates S j := by
  let grading := MvPolynomial.homogeneousSubmodule coordinates (ULift.{u} ℤ)
  letI : GradedRing grading := MvPolynomial.gradedAlgebra
  have h := Proj.basicOpen_ratio grading Nat.one_pos
    (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
    (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)
  rw [coordRatio, ← Scheme.preimage_basicOpen]
  change (toIntegralModel coordinates S) ⁻¹ᵁ
      (Proj grading).basicOpen (Proj.ratio grading
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) i)
        (MvPolynomial.X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j)) = _
  rw [h, Scheme.Hom.preimage_inf]
  rfl

end ZInQ.Contrib.CloudR2Poincare.L2
