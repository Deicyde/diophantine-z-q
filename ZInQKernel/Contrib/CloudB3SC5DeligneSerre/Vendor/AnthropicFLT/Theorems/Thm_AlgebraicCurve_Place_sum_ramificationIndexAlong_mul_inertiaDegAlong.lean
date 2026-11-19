/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong (git blob 7f938906324812b048c20e527f89f58054337666, sha256 bf2c2c59e4a261b3ad6b200f82b4e8cf44358e23ced94e3588e56fc84ef693e5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (v : Place K F) : ∑ w ∈ Place.fiberAlong φ hφ v, (w.ramificationIndexAlong φ : ℤ) * (w.inertiaDegAlong φ hφ : ℤ) = (finrankAlong K φ : ℤ) := by
  revert K F F' φ hφ hfin hsep v
  exact @_root_.P2MW.S_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong.solution
