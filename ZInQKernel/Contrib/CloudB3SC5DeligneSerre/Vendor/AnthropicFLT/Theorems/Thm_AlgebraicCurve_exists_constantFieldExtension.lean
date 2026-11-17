/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension (git blob 77a8cfea4705369b2f0f3f63f9c9effcb32d5625, sha256 0a98a3db164490b2d978e996cd33484ec841b197ccf698f051b61c50c469ca57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

universe u v w
theorem AlgebraicCurve.exists_constantFieldExtension (K₀ : Type u) (F₀ : Type v) (K' : Type w)
    [Field K₀] [Field F₀] [Field K'] [Algebra K₀ F₀] [Algebra K₀ K']
    [IsAlgClosed K₀] [CharZero K₀] [IsAlgClosed K']
    (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
    [IsCurveOver K₀ F₀] [HasCanonicalDivisor (K := K₀) (F := F₀)] :
    ∃ (F' : Type (max v w)) (_ : Field F') (_ : Algebra K' F') (_ : Algebra F₀ F')
      (_ : Algebra K₀ F') (_ : IsScalarTower K₀ K' F') (_ : IsScalarTower K₀ F₀ F')
      (_ : IsCurveOver K' F') (_ : HasCanonicalDivisor (K := K') (F := F')),
      (∃ x : F', Transcendental K' x ∧
        FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F') ∧
      IntermediateField.adjoin K' (Set.range (algebraMap F₀ F')) = ⊤ := by
  revert K₀ F₀ K' hfg₀
  exact @_root_.P2MW.S_AlgebraicCurve_exists_constantFieldExtension.solution
