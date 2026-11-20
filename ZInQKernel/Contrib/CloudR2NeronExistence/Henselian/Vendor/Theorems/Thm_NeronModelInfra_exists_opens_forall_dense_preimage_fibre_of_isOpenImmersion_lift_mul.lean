import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul.lean
Original Git blob: eb18da6080ea86ac582b89fb6a020439f09af632
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul

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

theorem NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base) :
    ∃ (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W),
      (∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X') ∧
      (∀ x : X, f.base x = IsLocalRing.closedPoint R →
        (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X') ∧
      (∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U) ∧
      (∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
        m.1.base ⟨q, hUW hq⟩ ∈ X') ∧
      (∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isOpenImmersion_lift_mul.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
