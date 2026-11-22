import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top.lean
Original Git blob: afa73db9de75abae5b1c775c7d62606eba03fc36
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top

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

theorem IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Finite ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
    {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module R (Mi i)]
    (fi : ∀ i, M →ₗ[R] Mi i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (fi i)]
    {Mij : ι → ι → Type*} [∀ i j, AddCommGroup (Mij i j)] [∀ i j, Module R (Mij i j)]
    (fij : ∀ i j, M →ₗ[R] Mij i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g i * g j)) (fij i j)]
    (ρ : ∀ i j, Mi i →ₗ[R] Mij i j) (ρ' : ∀ i j, Mi j →ₗ[R] Mij i j)
    (hρ : ∀ i j, (ρ i j).comp (fi i) = fij i j) (hρ' : ∀ i j, (ρ' i j).comp (fi j) = fij i j)
    (m : ∀ i, Mi i) (hm : ∀ i j, ρ i j (m i) = ρ' i j (m j)) :
    ∃! x : M, ∀ i, fi i x = m i := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
