import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.lean
Original Git blob: 2d0fe7e86af0e89b36d6e0c71f8fe365c3e6c337
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

h77_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~exists_isAffineHom_isIso_morphismRestrict_iso_affineDilatation_of_isClosed"

universe u

theorem NeronModelInfra.exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (t : ℕ) (Y : ℕ → Set X) (hY : ∀ i, IsClosed (Y i)) (hanti : ∀ i, Y (i + 1) ⊆ Y i) (hYt : Y t = ∅)
    (hYs : ∀ y ∈ Y 0, f y = IsLocalRing.closedPoint R) :
    ∃ (X₁ : Scheme.{u}) (v : X₁ ⟶ X),
      IsSeparated v ∧ LocallyOfFiniteType v ∧ QuasiCompact v ∧
      IsIso (pullback.map (v ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) v
        (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)) ∧
      IsIso (v ∣_ ⟨(Y 0)ᶜ, (hY 0).isOpen_compl⟩) ∧
      (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
        Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f,
          ∃! x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f), x₁.1 ≫ v = x.1) ∧
      (∀ (i : ℕ), i < t → ∀ (U : X.Opens) (hU : IsAffineOpen U), (∀ y ∈ (U : Set X), y ∉ Y (i + 1)) →
        ∀ (π : R), IsLocalRing.maximalIdeal R = Ideal.span {π} →
        ∃ (W : X₁.Opens)
          (e : (W : Scheme.{u}) ≅
            Spec (CommRingCat.of (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))),
          W.ι ≫ v = e.hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (AffineDilatation.Ring
              (PrimeSpectrum.vanishingIdeal ((fun y : U => hU.primeIdealOf y) '' {y : U | (y : X) ∈ Y i}))
              ((X.presheaf.map (homOfLE le_top).op).hom
                (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom π)))))) ≫ hU.fromSpec ∧
          ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'],
            Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' →
            ∀ x₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (v ≫ f),
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ Y i →
              (x₁.1 ≫ v) (IsLocalRing.closedPoint R') ∈ U →
              x₁.1 (IsLocalRing.closedPoint R') ∈ W) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_hom_isIso_morphismRestrict_compl_iso_affineDilatation_of_antitone_isClosed.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
