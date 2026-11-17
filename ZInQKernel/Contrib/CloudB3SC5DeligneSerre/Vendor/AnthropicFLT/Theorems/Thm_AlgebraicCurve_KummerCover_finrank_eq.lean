/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_KummerCover_finrank_eq (git blob d0497ec8c1c9e1314f7bc4d933c46a9be867b206, sha256 339062479e9214f41af7525b77dabefaa20aabbb2318a8d5200c1bb0f4ecb642).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.KummerExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_KummerCover_finrank_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial
theorem AlgebraicCurve.KummerCover.finrank_eq {F L : Type*} [Field F] [Field L] [Algebra F L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p ≠ f) :
    Module.finrank F L = p := by
  revert F L p hp f hζ hf
  exact @_root_.P2MW.S_AlgebraicCurve_KummerCover_finrank_eq.solution
