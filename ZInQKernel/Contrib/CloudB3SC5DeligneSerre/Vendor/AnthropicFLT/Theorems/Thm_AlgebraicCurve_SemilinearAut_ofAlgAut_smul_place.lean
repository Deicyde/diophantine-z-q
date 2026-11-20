/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place (git blob c78c8bc690f958a347d3a70137965c87a4e9ce5a, sha256 4ba35247bf067859105abf35714ea003bc8a0a4cd0697a3823db1988bf2bdb89).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.SemilinearAut.ofAlgAut_smul_place {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F) : ofAlgAut σ • v = σ • v := by
  revert K F σ v
  exact @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place.solution
