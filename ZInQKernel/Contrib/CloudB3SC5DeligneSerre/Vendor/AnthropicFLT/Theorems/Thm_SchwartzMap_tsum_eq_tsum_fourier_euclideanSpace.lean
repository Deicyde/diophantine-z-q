/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace (git blob bfdb9dfffca31556405fa034d87e856795262e00, sha256 3435af89b4049d1ff193526fbd4439b7ea5172079fb03e7acecede8c035658ed).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped FourierTransform InnerProductSpace SchwartzMap
theorem SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace
    {ι : Type*} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by
  revert ι f x
  exact @_root_.P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.solution
