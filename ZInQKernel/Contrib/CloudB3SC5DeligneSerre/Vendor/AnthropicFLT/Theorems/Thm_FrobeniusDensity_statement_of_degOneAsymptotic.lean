/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_statement_of_degOneAsymptotic (git blob dca9dc92b098d3a6a6e3760d084f9bedc7ceb38d, sha256 c747ce37086a42f287561a0c9fe82d349268e681f75f2d7a108a4186a6fc1011).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_statement_of_degOneAsymptotic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField
theorem FrobeniusDensity.statement_of_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (hL : FrobeniusDensity.DegOneAsymptotic L) :
    FrobeniusDensity.Statement L := by
  revert L hL
  exact @_root_.P2MW.S_FrobeniusDensity_statement_of_degOneAsymptotic.solution
