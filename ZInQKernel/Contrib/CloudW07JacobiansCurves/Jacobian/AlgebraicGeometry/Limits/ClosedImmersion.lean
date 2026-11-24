-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Limits.ClosedImmersion), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Limits.Finite
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Limits.Monomorphism
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Closed immersions at a finite stage

A finite type stage morphism that is a closed immersion after base change
to an affine-transition inverse limit is a closed immersion at a finite stage.
The proof combines eventual finiteness and eventual monomorphy.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem property_overPullback_comp
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S T U : Scheme.{u}} (a : U ⟶ T) (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y)
    (h : P ((Over.pullback b).map f).left) :
    P ((Over.pullback (a ≫ b)).map f).left := by
  have h' := P.overPullbackMap a ((Over.pullback b).map f) h
  let e := Over.pullbackComp a b
  let eX := (Over.forget U).mapIso (e.app X)
  let eY := (Over.forget U).mapIso (e.app Y)
  apply (P.arrow_mk_iso_iff (Arrow.isoMk eX eY ?_)).mpr h'
  exact (congrArg Over.Hom.left (e.hom.naturality f)).symm

/-- A finite type map that is closed over the inverse limit is closed at a finite stage. -/
theorem Scheme.exists_isClosedImmersion_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left) :
    ∃ (i : I) (h : i₀ ≤ i),
      IsClosedImmersion
        ((Over.pullback (D.map (homOfLE h).op)).map f₀).left := by
  have : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left := hf
  obtain ⟨i, hi, hfinite⟩ := Scheme.exists_isFinite_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀
    (inferInstance : IsFinite ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨j, hj, hmono⟩ := Scheme.exists_mono_baseChange_of_isLimit D c hc i₀ X₀ Y₀ f₀
    (inferInstance : Mono ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, hi.trans hik, ?_⟩
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  constructor
  · have H := property_overPullback_comp (@IsFinite)
      (D.map (homOfLE hik).op) (D.map (homOfLE hi).op) f₀ hfinite
    have he : D.map (homOfLE hik).op ≫ D.map (homOfLE hi).op =
        D.map (homOfLE (hi.trans hik)).op := by
      rw [← Functor.map_comp]
      rfl
    rwa [he] at H
  · have H := property_overPullback_comp (MorphismProperty.monomorphisms Scheme.{u})
      (D.map (homOfLE hjk).op) (D.map (homOfLE hj).op) f₀ hmono
    have he : D.map (homOfLE hjk).op ≫ D.map (homOfLE hj).op =
        D.map (homOfLE (hi.trans hik)).op := by
      rw [← Functor.map_comp]
      rfl
    rw [he] at H
    exact H

end AlgebraicGeometry
end
