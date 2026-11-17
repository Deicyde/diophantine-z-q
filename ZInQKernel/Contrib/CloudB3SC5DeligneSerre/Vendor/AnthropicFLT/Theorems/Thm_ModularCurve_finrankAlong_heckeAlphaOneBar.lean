/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrankAlong_heckeAlphaOneBar (git blob 83b5744f1e82f770b8d37e09871f598430aaf088, sha256 e4b9760abfaad0fd6b4e6c95a28cebbf12d4238a4b0d23184d9cab2f9222010e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrankAlong_heckeAlphaOneBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.finrankAlong_heckeAlphaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (q : ℕ) [Fact q.Prime] :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaOneBar L M q) =
      if q ∣ M then q else q + 1 := by
  revert L M q
  exact @_root_.P2MW.S_ModularCurve_finrankAlong_heckeAlphaOneBar.solution
