import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth.lean
Original Git blob: 6e070edf0f4914b5be72115b6e30917abb169bf3
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_of_isPullback_of_flat_of_surjective
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_one_comp_eq
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace GroupEquidimGC3
h77_bridge_namespace

theorem of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) : ∃ d : ℕ, SmoothOfRelativeDimension d g := by
  classical
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g

  let e : Spec (CommRingCat.of K) ⟶ X := (L.one (𝟙 _)).1
  obtain ⟨V₀, d, he, hV₀⟩ := AlgebraicGeometry.Smooth.exists_mem_and_smoothOfRelativeDimension_opensInclusion_comp g (e.base (IsLocalRing.closedPoint K))
  refine ⟨d, ?_⟩

  let S : Set X.Opens := {V | SmoothOfRelativeDimension d (V.ι ≫ g)}
  have hcov : (⨆ V : S, (V : X.Opens)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -

    by_contra hz
    have hzW : ∀ z' : X, z ⤳ z' → z' ∉ (⨆ V : S, (V : X.Opens)) := fun z' hzz' hz' =>
      hz (hzz'.mem_open (⨆ V : S, (V : X.Opens)).isOpen hz')
    obtain ⟨c, hccl, hcc⟩ := nonempty_inter_closedPoints (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
    rw [mem_closedPoints_iff] at hcc
    apply hzW c (specializes_iff_mem_closure.mpr hccl)
    let a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) g := ⟨pointOfClosedPoint g c hcc, pointOfClosedPoint_comp g c hcc⟩
    obtain ⟨τ, hτg, hτe⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_one_comp_eq L a

    let V₁ : X.Opens := τ.inv ⁻¹ᵁ V₀
    have hτg' : τ.inv ≫ g = g := by rw [← cancel_epi τ.hom, ← Category.assoc, τ.hom_inv_id, Category.id_comp, hτg]
    have hV₁ : SmoothOfRelativeDimension d (V₁.ι ≫ g) := by
      have h1 : V₁.ι ≫ g = (τ.inv ∣_ V₀) ≫ (V₀.ι ≫ g) := by
        show (τ.inv ⁻¹ᵁ V₀).ι ≫ g = _
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hτg']
      rw [h1]
      have := hV₀
      have h2 : SmoothOfRelativeDimension (0 + d) ((τ.inv ∣_ V₀) ≫ (V₀.ι ≫ g)) := inferInstance
      simpa using h2
    have hc : c ∈ V₁ := by
      show τ.inv.base c ∈ V₀
      have : τ.inv.base c = e.base (IsLocalRing.closedPoint K) := by
        rw [← pointOfClosedPoint_apply g c hcc (IsLocalRing.closedPoint K)]
        show (a.1 ≫ τ.inv).base _ = _
        rw [← hτe, Category.assoc, τ.hom_inv_id, Category.comp_id]
      rw [this]; exact he
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V₁, hV₁⟩, hc⟩
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) _ hcov fun V => V.2

end GroupEquidimGC3

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of K)} [Smooth g]
    (L : RelativeGroupLaw K g) :
    ∃ d : ℕ, SmoothOfRelativeDimension d g := by

  let Kb : Type u := AlgebraicClosure K
  let ι : Spec (CommRingCat.of Kb) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Kb))
  haveI : Smooth (pullback.snd g ι) := inferInstance
  obtain ⟨d, hd⟩ := GroupEquidimGC3.of_isAlgClosed ((ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.baseChange ι L))
  haveI := hd
  haveI : Flat ι := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : Surjective ι := ⟨fun p => ⟨IsLocalRing.closedPoint Kb, Subsingleton.elim _ _⟩⟩
  exact ⟨d, SmoothOfRelativeDimension.of_isPullback_of_flat_of_surjective d (IsPullback.of_hasPullback g ι).flip⟩


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
