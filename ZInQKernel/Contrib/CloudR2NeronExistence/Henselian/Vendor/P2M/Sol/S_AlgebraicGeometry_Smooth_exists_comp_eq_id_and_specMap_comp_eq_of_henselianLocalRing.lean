import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing.lean
Original Git blob: 7c1e4e94fdba13ff7e9a8dca0fb2de7b0793ac19
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open IsLocalRing CategoryTheory AlgebraicGeometry

namespace HenselSmoothSection
h77_bridge_namespace

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

theorem exists_lift_of_smooth
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, ∀ s, algebraMap R (ResidueField R) (ψ s) = φ s := by
  haveI := RingHom.ker_isPrime φ
  exact HenselianLocalRing.exists_algHom_lift_of_isSmoothAt S φ

theorem exists_section {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (ResidueField R))) ≫ s = x₀ := by

  let x : X := x₀.base (IsLocalRing.closedPoint (ResidueField R))
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let ι : Spec Γ(X, V) ⟶ X := hV.fromSpec

  have hrange : Set.range x₀.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = IsLocalRing.closedPoint (ResidueField R) := Subsingleton.elim _ _
    rw [hV.range_fromSpec]
    exact hxV
  let y₀ : Spec (CommRingCat.of (ResidueField R)) ⟶ Spec Γ(X, V) :=
    IsOpenImmersion.lift ι x₀ hrange
  have hy₀ : y₀ ≫ ι = x₀ := IsOpenImmersion.lift_fac ι x₀ hrange

  let g : Spec Γ(X, V) ⟶ Spec (CommRingCat.of R) := ι ≫ f
  let φ : CommRingCat.of R ⟶ Γ(X, V) := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  let π : Γ(X, V) ⟶ CommRingCat.of (ResidueField R) := Spec.preimage y₀
  have hπ : Spec.map π = y₀ := Spec.map_preimage y₀
  have hcomp : φ ≫ π = CommRingCat.ofHom (algebraMap R (ResidueField R)) := by
    rw [← Spec.map_inj, Spec.map_comp, hπ, hφ]
    change y₀ ≫ ι ≫ f = _
    rw [← Category.assoc, hy₀, hx₀]

  have hs : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hs

  letI : Algebra R Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.Smooth R Γ(X, V) := hs
  let πa : Γ(X, V) →ₐ[R] ResidueField R :=
    { π.hom with
      commutes' := fun r => by
        change π.hom (φ.hom r) = algebraMap R (ResidueField R) r
        rw [← CommRingCat.comp_apply, hcomp]
        rfl }
  obtain ⟨ψ, hψ⟩ := exists_lift_of_smooth (R := R) Γ(X, V) πa
  have hψφ : φ ≫ CommRingCat.ofHom ψ.toRingHom = 𝟙 _ := by
    ext r
    change ψ (φ.hom r) = r
    exact ψ.commutes r
  have hψπ : CommRingCat.ofHom ψ.toRingHom ≫
      CommRingCat.ofHom (algebraMap R (ResidueField R)) = π := by
    ext a
    exact hψ a
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ι, ?_, ?_⟩
  · change Spec.map _ ≫ g = 𝟙 _
    rw [← hφ, ← Spec.map_comp, hψφ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψπ, hπ, hy₀]

end HenselSmoothSection

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s = x₀ :=
  HenselSmoothSection.exists_section f x₀ hx₀


end P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
