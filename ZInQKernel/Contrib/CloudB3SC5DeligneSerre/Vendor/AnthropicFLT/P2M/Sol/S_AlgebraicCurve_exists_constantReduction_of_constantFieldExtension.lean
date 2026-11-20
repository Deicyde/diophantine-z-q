/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension (git blob a378efe5cf8350953aabb9374d77d075c1fe3457, sha256 a1cb036b14c77d79f0b5001d7ff1d07ded8ef7cc256b98353298187759ef7463).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_valuationSubring_section_of_constantField_valuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension

open AlgebraicCurve

theorem solution
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤) :
    ∃ (O : ValuationSubring F') (ρ : O →+* F),
      (∀ f : F, ∃ h : algebraMap F F' f ∈ O, ρ ⟨algebraMap F F' f, h⟩ = f) ∧
      RingHom.ker ρ = IsLocalRing.maximalIdeal O ∧
      (∀ f' : F', f' ≠ 0 → ∃ c : K', ∃ h : c • f' ∈ O, ρ ⟨c • f', h⟩ ≠ 0) ∧
      (∀ (c : K') (h : algebraMap K' F' c ∈ O),
        ρ ⟨algebraMap K' F' c, h⟩ ∈ Set.range (algebraMap K F)) := by

  obtain ⟨A, hK, σ, hker, hsec⟩ :=
    IsAlgClosed.exists_valuationSubring_ringHom_retraction K K'

  exact AlgebraicCurve.exists_valuationSubring_section_of_constantField_valuationSubring
    K F K' F' hfg hfg' hgen A hK σ hker hsec
