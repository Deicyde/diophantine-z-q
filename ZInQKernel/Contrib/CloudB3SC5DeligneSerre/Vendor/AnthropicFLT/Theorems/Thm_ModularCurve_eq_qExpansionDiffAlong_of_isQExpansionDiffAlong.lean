/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong (git blob 21fc808618d88f727bad29cd1f502e312b0c5f26, sha256 a6ba16586cd695ca6308b999cc30b28ad7b781979b7e567c7bcc42ce61848aed).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) : φ = qExpansionDiffAlong σ := by
  revert K F L σ φ hφ
  exact @_root_.P2MW.S_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong.solution
