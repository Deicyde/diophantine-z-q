/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_finset (git blob e0cc7ac9d254a3c930b119befb21601264a6ee6f, sha256 6f9915d4e9ec2202520f4dd0f82e58a49e4d31b7e43d4fa979d5f760b860d459).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_constantFieldDescent_finset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

universe u v

theorem AlgebraicCurve.exists_constantFieldDescent_finset (K : Type u) (F : Type v)
    [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] (t : Finset F) :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀)
      (_ : Algebra K₀ F₀) (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : Algebra K₀ ℂ)
      (_ : IsAlgClosed K₀) (_ : Countable K₀) (_ : IsCurveOver K₀ F₀),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (↑t : Set F) ⊆ Set.range (algebraMap F₀ F) := by
  revert K F hfg t
  exact @_root_.P2MW.S_AlgebraicCurve_exists_constantFieldDescent_finset.solution
