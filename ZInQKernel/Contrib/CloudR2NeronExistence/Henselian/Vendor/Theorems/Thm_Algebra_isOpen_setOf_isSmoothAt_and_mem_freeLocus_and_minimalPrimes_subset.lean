import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset.lean
Original Git blob: bc055a6c157b972977dc61fb51c989f7b13b30ab
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

universe u

theorem Algebra.isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
    {k : Type u} [Field k] {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J : Ideal A)
    [Algebra k (A ⧸ J)] [Algebra.FiniteType k (A ⧸ J)] [IsReduced (A ⧸ J)]
    (S : Set (PrimeSpectrum (A ⧸ J)))
    (hdense : ∀ g : A ⧸ J, (∀ 𝔰 ∈ S, g ∈ 𝔰.asIdeal) → g = 0)
    (hsep : ∀ 𝔰 ∈ S, ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      Algebra.FormallySmooth k K ∧ Nonempty (𝔰.asIdeal.ResidueField →ₐ[k] K)) :
    IsOpen {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
      𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} ∧
    ∀ 𝔮 : PrimeSpectrum (A ⧸ J), 𝔮.asIdeal ∈ minimalPrimes (A ⧸ J) →
      Algebra.IsSmoothAt k 𝔮.asIdeal ∧ 𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
