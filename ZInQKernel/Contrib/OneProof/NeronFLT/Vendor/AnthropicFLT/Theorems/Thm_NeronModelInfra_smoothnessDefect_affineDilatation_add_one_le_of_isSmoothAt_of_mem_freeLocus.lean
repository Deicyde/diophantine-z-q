/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_SmoothnessDefect
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

theorem NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    {A : Type u} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    (J : Ideal A) (hπJ : algebraMap R A π ∈ J)
    [Algebra (IsLocalRing.ResidueField R) (A ⧸ J)] [IsScalarTower R (IsLocalRing.ResidueField R) (A ⧸ J)]
    (hN : ∀ g : A,
      (∀ (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R R'']
        [IsLocalHom (algebraMap R R'')], IsIndexOneExtension R R'' →
        ∀ c : A →ₐ[R] R'', J ≤ (IsLocalRing.maximalIdeal R'').comap c →
          g ∈ (IsLocalRing.maximalIdeal R'').comap c) → g ∈ J)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (hR' : IsIndexOneExtension R R')
    (φ : A →ₐ[R] R') (hgen : PrimeSpectrum.comap φ.toRingHom (⊥ : PrimeSpectrum R') ∈ Algebra.smoothLocus R A)
    (𝔮 : Ideal (A ⧸ J)) [𝔮.IsPrime] (h𝔮 : 𝔮.comap (Ideal.Quotient.mk J) = (IsLocalRing.maximalIdeal R').comap φ)
    (hsmooth : Algebra.IsSmoothAt (IsLocalRing.ResidueField R) 𝔮)
    (hfree : (⟨𝔮, ‹_›⟩ : PrimeSpectrum (A ⧸ J)) ∈
      Module.freeLocus (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    (φ' : AffineDilatation.Ring J (algebraMap R A π) →ₐ[R] R')
    (hφ' : ∀ a : A, φ' (algebraMap A (AffineDilatation.Ring J (algebraMap R A π)) a) = φ a) :
    smoothnessDefect
        (Spec.map (CommRingCat.ofHom (algebraMap R (AffineDilatation.Ring J (algebraMap R A π)))))
        (Spec.map (CommRingCat.ofHom φ'.toRingHom)) + 1 ≤
      max 1 (smoothnessDefect (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φ.toRingHom))) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus.solution
