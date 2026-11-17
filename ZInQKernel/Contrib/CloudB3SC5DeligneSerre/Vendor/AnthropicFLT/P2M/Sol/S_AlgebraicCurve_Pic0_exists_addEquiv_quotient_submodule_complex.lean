/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex (git blob 9a4a6e9832cb07c741a48c2f426c481e879adc61, sha256 f8fb777c5ceb6f0ea0f82487c37a15b1c4ac863abbea3251d462db23d811cf1c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_complex

set_option autoImplicit false

open AlgebraicCurve
open scoped Manifold ContDiff

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)] :
    ∃ (L : Submodule ℤ (Fin (genus ℂ F) → ℂ)),
      Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = 2 * genus ℂ F ∧
      Nonempty (Pic0 ℂ F ≃+ (Fin (genus ℂ F) → ℂ) ⧸ L) := by
  obtain ⟨_instTop, _instCharted, _instManifold, _instCompact, _instT2, _instConn, hF⟩ :=
    Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F hfg
  exact Pic0.exists_addEquiv_quotient_submodule_of_chartedSpace_complex F hfg hF
