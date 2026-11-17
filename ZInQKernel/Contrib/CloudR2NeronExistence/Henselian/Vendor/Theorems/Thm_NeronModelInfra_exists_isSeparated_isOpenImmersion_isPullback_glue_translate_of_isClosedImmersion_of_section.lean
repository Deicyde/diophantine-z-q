import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section.lean
Original Git blob: 487cc8a2920e374c4221f2d8c58e4520f705c0a9
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hγ : Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base ⊆
      Set.range γ.base)
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _) :
    ∃ (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧ IsOpenImmersion τ.1 ∧
      (∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base) ∧
      IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
          (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
