import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem.lean
Original Git blob: 7ae29130a012dc2a12d7f5977d03bdad45f292a2
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U) :
    letI : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ c : Γ(X, U) →ₐ[R] R',
      (IsLocalRing.maximalIdeal R').comap c = (hU.primeIdealOf ⟨x.1 (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
