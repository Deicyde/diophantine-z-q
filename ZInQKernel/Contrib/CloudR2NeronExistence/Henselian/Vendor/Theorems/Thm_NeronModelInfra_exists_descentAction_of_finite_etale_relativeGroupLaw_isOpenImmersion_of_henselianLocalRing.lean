import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.lean
Original Git blob: 8286fe3dd906feaf2e0f4f93aed1a374b0295db8
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_DescentAction
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing

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

theorem NeronModelInfra.exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b) jY')) :
    ∃ A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g',
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫ jY'.1 ∧
      (∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
