import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis.lean
Original Git blob: 3abe356bbfa49976d088e3cb4dbf836d643e9338
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis

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

theorem AffineDilatation.exists_basis_kaehlerDifferential_of_smooth_of_basis
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C : Type u} [CommRing C] [Algebra R C] [Algebra.Smooth R C]
    {r n : ℕ} (y : Fin r → C) (z : Fin n → C) (b : Module.Basis (Fin r ⊕ Fin n) C Ω[C⁄R])
    (hby : ∀ i, b (Sum.inl i) = D R C (y i)) (hbz : ∀ j, b (Sum.inr j) = D R C (z j)) :
    ∃ b' : Module.Basis (Fin r ⊕ Fin n)
        (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
        Ω[AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)⁄R],
      (∀ i, b' (Sum.inl i) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (y i))) ∧
      (∀ j, (algebraMap R
          (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π)) π) •
          b' (Sum.inr j) =
        D R (AffineDilatation.Ring (Ideal.span (insert (algebraMap R C π) (Set.range z))) (algebraMap R C π))
          (algebraMap C _ (z j))) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AffineDilatation_exists_basis_kaehlerDifferential_of_smooth_of_basis.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
