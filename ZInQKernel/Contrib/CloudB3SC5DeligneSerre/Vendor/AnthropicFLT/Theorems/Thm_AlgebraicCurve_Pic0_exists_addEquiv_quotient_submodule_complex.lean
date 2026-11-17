/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex (git blob 01a5251a052a297f181becd528cf9b5508a9a078, sha256 c3cbef3caea43243e1d03ac0e206ec7cb94ff752ddece45a541119dc1900cb41).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_addEquiv_quotient_submodule_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)] :
    ∃ (L : Submodule ℤ (Fin (genus ℂ F) → ℂ)),
      Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = 2 * genus ℂ F ∧
      Nonempty (Pic0 ℂ F ≃+ (Fin (genus ℂ F) → ℂ) ⧸ L) := by
  revert F hfg
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex.solution
