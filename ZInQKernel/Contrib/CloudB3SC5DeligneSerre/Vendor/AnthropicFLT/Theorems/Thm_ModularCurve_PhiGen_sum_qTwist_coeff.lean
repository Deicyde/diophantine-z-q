/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_sum_qTwist_coeff (git blob 8cf26db80b3b43c9fa60860f7f8b06a0f457354a, sha256 36f94f56764838823d38e8155e7621ea1da247a185961ea9315b28ca19494f90).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_sum_qTwist_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.sum_qTwist_coeff {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) (f : LaurentSeries K) (k : ℤ) : (∑ b ∈ Finset.range ℓ, qTwist (ζ ^ b) f).coeff k = if (ℓ : ℤ) ∣ k then (ℓ : K) * f.coeff k else 0 := by
  revert K ℓ ζ hζ f k
  exact @_root_.P2MW.S_ModularCurve_PhiGen_sum_qTwist_coeff.solution
