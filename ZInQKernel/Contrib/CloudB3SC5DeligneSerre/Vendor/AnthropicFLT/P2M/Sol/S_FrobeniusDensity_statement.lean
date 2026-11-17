/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_statement (git blob 544b5cbac650d2433aaba8eda1f5d1e14123582b, sha256 3fbb7970eaa38722dce233609da11711489b1d1ddbe2956fa93c0b85bdec7a02).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_degOneAsymptotic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_statement_of_degOneAsymptotic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_FrobeniusDensity_statement

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.Statement L :=
  FrobeniusDensity.statement_of_degOneAsymptotic L (FrobeniusDensity.degOneAsymptotic L)
