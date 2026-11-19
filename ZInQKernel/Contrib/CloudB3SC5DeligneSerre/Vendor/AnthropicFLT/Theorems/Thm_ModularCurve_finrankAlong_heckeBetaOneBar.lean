/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar (git blob 2c8cb635c9410d42728f15b39c2055bf05a59520, sha256 23422cd6dc7e259a98d05085a26f8b099ff7c1cd1d32772489907e4fd3a71b26).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrankAlong_heckeBetaOneBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.finrankAlong_heckeBetaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (h : ModularCurve.HeckeBetaOneDefined M ℓ) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeBetaOneBar L M ℓ) =
      if ℓ ∣ M then ℓ else ℓ + 1 := by
  revert L M ℓ h
  exact @_root_.P2MW.S_ModularCurve_finrankAlong_heckeBetaOneBar.solution
