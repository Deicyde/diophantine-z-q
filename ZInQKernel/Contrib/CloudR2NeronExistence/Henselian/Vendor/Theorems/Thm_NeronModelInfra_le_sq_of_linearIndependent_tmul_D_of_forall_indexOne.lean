import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne.lean
Original Git blob: cd729ef8e9e54af46fba5091bfd066e807a765e7
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne

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

open TensorProduct KaehlerDifferential NeronModelInfra

universe u

theorem NeronModelInfra.le_sq_of_linearIndependent_tmul_D_of_forall_indexOne
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    {n : ℕ} (z : Fin n → C)
    (hIJ : RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)))
    (hlin : LinearIndependent (C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z)))
      fun j : Fin n => (1 : C ⧸ Ideal.span (insert (algebraMap R C π) (Set.range z))) ⊗ₜ[C]
        D R A (algebraMap C A (z j)))
    (hN : ∀ g : C,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : C →ₐ[R] R'', RingHom.ker (algebraMap C A) ≤ RingHom.ker c.toRingHom →
          Ideal.span (insert (algebraMap R C π) (Set.range z)) ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) →
      g ∈ Ideal.span (insert (algebraMap R C π) (Set.range z))) :
    RingHom.ker (algebraMap C A) ≤ Ideal.span (insert (algebraMap R C π) (Set.range z)) ^ 2 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_le_sq_of_linearIndependent_tmul_D_of_forall_indexOne.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
