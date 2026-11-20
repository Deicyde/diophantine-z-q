import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq.lean
Original Git blob: c02e3dc8444224c4fa38a8f1e729da8e528feab6
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])) := by
  classical

  obtain ⟨U, hU, V, hV, hyV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) y

  obtain ⟨r, s, hys, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n).away
    y ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ ⟨V, hV⟩ ⟨V, hV⟩ hyV hyV e hf (by trivial)
  set W : Y.Opens := Y.basicOpen s with hW
  have hWaff : IsAffineOpen W := hV.basicOpen s
  have hyW : y ∈ W := hys
  have eW : W ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := fun x _ => by simp

  letI algA : Algebra R Γ(Y, W) := ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom.toAlgebra

  letI algAs : Algebra Γ(Y, W) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk ⟨y, hyW⟩
  have hpin : CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
    have h := congrArg Scheme.Hom.appTop halg
    rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h

    have h' := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom) h
    simp only [Category.assoc] at h'
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc] at h'
    simpa using h'.symm
  haveI : IsScalarTower R Γ(Y, W) (Y.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq fun a => by
    show (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))).hom a =
      (Y.presheaf.germ W y hyW).hom (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ W eW).hom a)
    rw [hpin, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE, Category.assoc,
      TopCat.Presheaf.germ_res]
    rfl

  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(Y, W) := by
    have h₁ := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h₁
    have h₂ : (f.appLE ⊤ W eW).hom.IsStandardSmoothOfRelativeDimension n := h₁
    have h₃ := ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).cancel_left_isIso
      (Scheme.ΓSpecIso (.of R)).inv (f.appLE ⊤ W eW)).mpr h₂
    rw [← CommRingCat.hom_comp] at h₃
    exact h₃
  haveI := hstd
  haveI : Algebra.IsStandardSmooth R Γ(Y, W) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : Nontrivial Γ(Y, W) := (algebraMap Γ(Y, W) (Y.presheaf.stalk y)).domain_nontrivial
  have hrank : Module.rank Γ(Y, W) Ω[Γ(Y, W)⁄R] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  haveI : Module.Finite Γ(Y, W) Ω[Γ(Y, W)⁄R] := Module.finite_of_rank_eq_nat hrank
  let bA : Module.Basis (Fin n) Γ(Y, W) Ω[Γ(Y, W)⁄R] :=
    Module.finBasisOfFinrankEq _ _ (Module.finrank_eq_of_rank_eq hrank)

  haveI := hWaff.isLocalization_stalk ⟨y, hyW⟩
  exact ⟨bA.ofIsLocalizedModule (Y.presheaf.stalk y) (hWaff.primeIdealOf ⟨y, hyW⟩).asIdeal.primeCompl
    (KaehlerDifferential.map R R Γ(Y, W) (Y.presheaf.stalk y))⟩


end P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
