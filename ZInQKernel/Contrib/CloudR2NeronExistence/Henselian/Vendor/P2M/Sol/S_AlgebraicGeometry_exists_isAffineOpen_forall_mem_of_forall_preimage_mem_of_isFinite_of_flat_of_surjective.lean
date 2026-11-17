import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective.lean
Original Git blob: eef3c24a829ad4773d59cdd532513de77ec907f4
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mFlfDescAF
h77_bridge_namespace

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

theorem hmono {T : Scheme.{u}} (a b : T ⟶ pullback p p)
    (h₁ : a ≫ pullback.fst p p = b ≫ pullback.fst p p) (h₂ : a ≫ pullback.snd p p = b ≫ pullback.snd p p) :
    a = b :=
  pullback.hom_ext h₁ h₂

theorem rel_iff {T : Scheme.{u}} (x y : T ⟶ X) :
    (∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y) ↔ x ≫ p = y ≫ p := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  · intro h
    exact ⟨pullback.lift x y h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem hequiv (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ X =>
      ∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y := by
  constructor
  · intro x
    exact (rel_iff p x x).2 rfl
  · intro x y h
    exact (rel_iff p y x).2 ((rel_iff p x y).1 h).symm
  · intro x y z h h'
    exact (rel_iff p x z).2 (((rel_iff p x y).1 h).trans ((rel_iff p y z).1 h'))

end P2mFlfDescAF

open P2mFlfDescAF in
theorem solution
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (S : Finset Y) (W : X.Opens) (hW : IsAffineOpen W) (hSW : ∀ x : X, p.base x ∈ S → x ∈ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ ∀ y ∈ S, y ∈ V := by
  classical

  have hfin : (p.base ⁻¹' (S : Set Y)).Finite := p.finite_preimage S.finite_toSet

  obtain ⟨W', hW'aff, hSW', -, hinv⟩ :=
    AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finite_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst p p) (pullback.snd p p) (hequiv p) hfin hW (fun x hx r hr => by
        apply hSW
        have hc : p.base ((pullback.snd p p).base r) = p.base ((pullback.fst p p).base r) := by
          change (pullback.snd p p ≫ p).base r = (pullback.fst p p ≫ p).base r
          rw [pullback.condition]
        rw [hc]
        have hr' : (pullback.fst p p).base r = x := hr
        rw [hr']
        exact hx)

  obtain ⟨V, hV, hpV⟩ :=
    AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant (pullback.fst p p) (pullback.snd p p)
      (fun a b h₁ h₂ => hmono p a b h₁ h₂) (hequiv p) p pullback.condition (IsPullback.of_hasPullback p p)
      W' hW'aff hinv
  refine ⟨V, hV, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := p.surjective y
  have hx : x ∈ (W' : Set X) := hSW' (show x ∈ p.base ⁻¹' (S : Set Y) from hy)
  have hx' : x ∈ p ⁻¹ᵁ V := by rw [hpV]; exact hx
  exact hx'


end P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_preimage_mem_of_isFinite_of_flat_of_surjective
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
