/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_statement (git blob 4ccc49ecf9ed895a97e6fc985d9473683f74c237, sha256 f3da80f33e92d5d1d088a97c9c330a5b564df7fa83af4c6d50140d727aa0c553).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_statement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField
theorem FrobeniusDensity.statement (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L := by
  revert L
  exact @_root_.P2MW.S_FrobeniusDensity_statement.solution
