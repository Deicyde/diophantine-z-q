/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_Algebra_isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Algebra_isOpen_setOf_isSmoothAt_and_mem_freeLocus_and_minimalPrimes_subset

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
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
      Algebra.IsSmoothAt k 𝔮.asIdeal ∧ 𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
  classical
  haveI : Algebra.FinitePresentation k (A ⧸ J) := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨?_, ?_⟩
  · have h1 : IsOpen (Algebra.smoothLocus k (A ⧸ J)) := Algebra.isOpen_smoothLocus
    have h2 : IsOpen (Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)) := Module.isOpen_freeLocus
    have : {𝔮 : PrimeSpectrum (A ⧸ J) | Algebra.IsSmoothAt k 𝔮.asIdeal ∧
        𝔮 ∈ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M)} =
        Algebra.smoothLocus k (A ⧸ J) ∩ Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] M) := by
      ext 𝔮; rfl
    rw [this]
    exact h1.inter h2
  · intro 𝔮 h𝔮
    refine ⟨Algebra.isSmoothAt_of_mem_minimalPrimes_of_dense_of_formallySmooth_residueField S hdense hsep 𝔮.asIdeal h𝔮, ?_⟩
    rw [Module.mem_freeLocus]
    haveI : Ring.KrullDimLE 0 (Localization.AtPrime 𝔮.asIdeal) :=
      Ring.KrullDimLE.of_isLocalization 𝔮.asIdeal h𝔮 (Localization.AtPrime 𝔮.asIdeal)
    letI hF : Field (Localization.AtPrime 𝔮.asIdeal) := Ring.KrullDimLE.isField_of_isReduced.toField
    exact Module.Free.of_divisionRing (Localization.AtPrime 𝔮.asIdeal) _
