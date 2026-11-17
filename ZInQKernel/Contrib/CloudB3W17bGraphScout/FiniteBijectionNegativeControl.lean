import Mathlib.Algebra.DualNumber
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-!
A negative control for the projection-iso tail, not a counterexample to H105.
A finite morphism in characteristic zero can be bijective on actual complex
points without being an algebraic isomorphism. Here the source has nilpotents
and is NOT a group scheme; the proved group/Cartier argument cannot be omitted.
-/

open CategoryTheory AlgebraicGeometry

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout
namespace NegativeControl

private abbrev D := DualNumber ℂ

private def dualLinearEquiv : D ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun x := (x.fst, x.snd)
  invFun x := TrivSqZeroExt.inl x.1 + TrivSqZeroExt.inr x.2
  left_inv x := x.inl_fst_add_inr_snd_eq
  right_inv x := by ext <;> simp
  map_add' x y := rfl
  map_smul' c x := rfl

private theorem eps_image_zero (f : D →ₐ[ℂ] ℂ) : f DualNumber.eps = 0 := by
  have h : f DualNumber.eps * f DualNumber.eps = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  exact mul_self_eq_zero.mp h

private theorem dual_algHom_subsingleton : Subsingleton (D →ₐ[ℂ] ℂ) := by
  constructor
  intro f g
  exact DualNumber.algHom_ext ((eps_image_zero f).trans (eps_image_zero g).symm)

private theorem dual_algebraMap_not_surjective :
    ¬ Function.Surjective (algebraMap ℂ D) := by
  intro h
  obtain ⟨c, hc⟩ := h DualNumber.eps
  have hs : (0 : ℂ) = 1 := congrArg (fun x : D => x.snd) hc
  exact zero_ne_one hs

/-- Finite and point-bijective over ℂ does not imply an isomorphism for arbitrary schemes.
This control uses the actual dual-number scheme and the native complex-point carrier. -/
theorem finite_bijective_complexPoints_not_iso :
    ∃ (X : Over (Spec (.of ℂ))) (p : X ⟶ Over.mk (𝟙 (Spec (.of ℂ)))),
      IsFinite p.left ∧ Function.Bijective (Point.map p) ∧ ¬ IsIso p.left := by
  let X : Over (Spec (.of ℂ)) := Over.mk (ComplexPoint.affineSpecStructureMap D)
  let p : X ⟶ Over.mk (𝟙 (Spec (.of ℂ))) :=
    Over.homMk (ComplexPoint.affineSpecStructureMap D) (by simp [X])
  haveI : Module.Finite ℂ D := Module.Finite.equiv dualLinearEquiv.symm
  have hfin : IsFinite p.left := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℂ D)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI : Subsingleton (D →ₐ[ℂ] ℂ) := dual_algHom_subsingleton
  haveI : Subsingleton (ComplexPoint X) := by
    constructor
    intro a b
    exact (ComplexPoint.affineSpecEquiv D).injective (Subsingleton.elim _ _)
  haveI : Subsingleton (ComplexPoint (Over.mk (𝟙 (Spec (.of ℂ))))) := by
    constructor
    intro a b
    apply Over.OverMorphism.ext
    have ha : a.left = 𝟙 (Spec (.of ℂ)) := by simpa using Over.w a
    have hb : b.left = 𝟙 (Spec (.of ℂ)) := by simpa using Over.w b
    exact ha.trans hb.symm
  have hbij : Function.Bijective (Point.map p) := by
    constructor
    · intro a b _
      exact Subsingleton.elim _ _
    · intro b
      exact ⟨(ComplexPoint.affineSpecEquiv D).symm (TrivSqZeroExt.fstHom ℂ ℂ ℂ),
        Subsingleton.elim _ _⟩
  refine ⟨X, p, hfin, hbij, ?_⟩
  intro hi
  have hmap : Function.Bijective (algebraMap ℂ D) := by
    exact isIso_SpecMap_iff.mp hi
  exact dual_algebraMap_not_surjective hmap.2

end NegativeControl
end ZInQ.Contrib.CloudB3W17bGraphScout
