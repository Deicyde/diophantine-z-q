import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd.lean
Original Git blob: f734a9f5332a4b4406107f268aff6363d961a539
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd
    {A : Type u} [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of A))
    (k : Type u) [CommRing k] [Algebra A k]
    (x : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k))))) :
    letI z := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).base x
    letI : Algebra A (X.presheaf.stalk z) :=
      ((X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).toAlgebra
    ∃ (𝔮 : Ideal ((X.presheaf.stalk z) ⊗[A] k)) (_ : 𝔮.IsPrime)
      (e : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.stalk x ≃+* Localization.AtPrime 𝔮),
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := X.presheaf.stalk z) (B := k)).toRingHom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      (∀ s : X.presheaf.stalk z,
        e (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).stalkMap x).hom s) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (s ⊗ₜ[A] 1)) ∧
      (∀ c : k,
        e ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).presheaf.germ ⊤ x trivial
            ((pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A k)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) =
          algebraMap ((X.presheaf.stalk z) ⊗[A] k) (Localization.AtPrime 𝔮) (1 ⊗ₜ[A] c)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_exists_ringEquiv_stalk_pullback_localization_tensorProduct_stalk_of_germ_snd.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
