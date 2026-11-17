import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField.lean
Original Git blob: a722d7cb20b494797518105a4bbce51ccfd226be
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential TensorProduct"
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct KaehlerDifferential

universe u

theorem Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (g : S) (_ : g ∉ u) (C : Type u) (_ : CommRing C) (_ : Algebra R C)
      (_ : Algebra C (Localization.Away g)) (_ : IsScalarTower R C (Localization.Away g)),
      Algebra.IsStandardSmooth R C ∧ Function.Surjective (algebraMap C (Localization.Away g)) ∧
      ∃ (W : ι → C) (b : Module.Basis ι C Ω[C⁄R]),
        (∀ i, algebraMap C (Localization.Away g) (W i) = algebraMap S (Localization.Away g) (w i)) ∧
        (∀ i, b i = D R C (W i)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
