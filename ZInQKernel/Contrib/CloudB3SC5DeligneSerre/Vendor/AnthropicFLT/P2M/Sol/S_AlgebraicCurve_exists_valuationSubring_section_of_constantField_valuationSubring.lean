/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring (git blob a854d18cb1999608657875458d9856c4fc3172e3, sha256 871006aa53a5bdf04b9838da288633021c2784bb6bf1e6fce96ac1bf581c8898).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_regularProlongation_retraction_of_constantField_valuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring

open AlgebraicCurve

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (hker : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    ∃ (O : ValuationSubring F') (ρ : O →+* F),
      (∀ f : F, ∃ h : algebraMap F F' f ∈ O, ρ ⟨algebraMap F F' f, h⟩ = f) ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal O ∧
      (∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ρ ⟨c • f', h⟩ ≠ 0) ∧
      (∀ (c : K') (h : algebraMap K' F' c ∈ O),
        ρ ⟨algebraMap K' F' c, h⟩ ∈ Set.range (algebraMap K F)) := by
  obtain ⟨O, ρ, hmem_iff, hker_ρ, hresA, hreg, hret⟩ :=
    AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring
      K F K' F' hfg hfg' hgen A hK σ hker hsec
  refine ⟨O, ρ, hret, hker_ρ, hreg, ?_⟩

  intro c hc
  obtain ⟨h', hρ⟩ := hresA ⟨c, (hmem_iff c).mp hc⟩
  exact ⟨σ ⟨c, (hmem_iff c).mp hc⟩, hρ.symm⟩
