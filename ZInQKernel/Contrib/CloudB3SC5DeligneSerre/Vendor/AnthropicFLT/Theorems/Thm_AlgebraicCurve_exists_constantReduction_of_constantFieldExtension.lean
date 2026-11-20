/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension (git blob 3b700c4fe5b260e60e85679fa878bfc78c11d6e0, sha256 71f2e2efe2702ba613ae1324865ce62a7b09dffe9a9bad25e86341b3e9283293).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AlgebraicCurve.exists_constantReduction_of_constantFieldExtension
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
  revert K F K' F' hfg hfg' hgen
  exact @_root_.P2MW.S_AlgebraicCurve_exists_constantReduction_of_constantFieldExtension.solution
