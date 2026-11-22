import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes.lean
Original Git blob: ed27737adfb66c88cc7718d85332d1b67c9ca1d3
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_Topology_IsConstructible_mem_of_mem_closure_of_forall_specializes
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Topology

universe u

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [CompactSpace Y] [QuasiSeparatedSpace Y] {C : Set X} (hC : Topology.IsConstructible C)
    {y : Y} (hy : y ∈ closure (f.base '' C)) (hgen : ∀ c ∈ C, y ⤳ f.base c) :
    y ∈ f.base '' C :=
  ZInQ.Contrib.CloudR2NeronExistence.Henselian.Topology.IsConstructible.mem_of_mem_closure_of_forall_specializes
    (f.isConstructible_image hC) hy
    (by rintro _ ⟨c, hc, rfl⟩; exact hgen c hc)


end P2MW.S_AlgebraicGeometry_mem_image_of_mem_closure_image_of_forall_specializes
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
