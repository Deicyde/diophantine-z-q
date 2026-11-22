import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.lean
Original Git blob: 1c31ff79affc9e07a30f251399511998238e355b
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section

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

theorem NeronModelInfra.exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (hΓa : pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y ≫ τ.1 =
          pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y ≫ ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ τ.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ τ.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : SchemeHomOver t y)
          (u v : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ U.ι ≫ pullback.snd y y = t ≫ a →
        v.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → v.1 ≫ U.ι ≫ pullback.snd y y = d.1 →
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = d.1 ≫ τ.1 ∧
          w'.1 ≫ m'.1 = v.1 ≫ m.1 ≫ ι.1) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
