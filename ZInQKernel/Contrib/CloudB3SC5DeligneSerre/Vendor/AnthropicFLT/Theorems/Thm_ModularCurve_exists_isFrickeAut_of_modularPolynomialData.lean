/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData (git blob 6edd4bd2b340215a395d1a525dbaefb7fdd9acda, sha256 57b87fb57e057b2881c9f4292e409b9eb7a1dd52e9c053bc0cdb0317168b0f30).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAut_of_modularPolynomialData {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (hsymm : EvalSymm data.Φ) (hirr : PhiIrreducible data) : ∃ σ : modularFunctionField N ≃ₐ[ℚ] modularFunctionField N, IsFrickeAut N σ := by
  revert N data hsymm hirr
  exact @_root_.P2MW.S_ModularCurve_exists_isFrickeAut_of_modularPolynomialData.solution
