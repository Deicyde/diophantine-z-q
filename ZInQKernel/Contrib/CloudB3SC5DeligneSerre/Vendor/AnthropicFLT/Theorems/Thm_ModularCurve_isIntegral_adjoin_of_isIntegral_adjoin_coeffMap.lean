/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap (git blob 8e47a4989dee28f2e9961a40ea4f0d19b082b98f, sha256 28d6961c5e42409708e2fc69c829cf56882242c4dd2a8819296028b269102679).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.isIntegral_adjoin_of_isIntegral_adjoin_coeffMap {k L : Type*} [Field k]
    [Field L] (σ : k →+* L) (j x : LaurentSeries k)
    (h : IsIntegral (Algebra.adjoin L ({coeffMap σ j} : Set (LaurentSeries L))) (coeffMap σ x)) :
    IsIntegral (Algebra.adjoin k ({j} : Set (LaurentSeries k))) x := by
  revert k L σ j x h
  exact @_root_.P2MW.S_ModularCurve_isIntegral_adjoin_of_isIntegral_adjoin_coeffMap.solution
