/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2 (git blob d5f594469f7780369fe7037ceb04163e80f8f3d8, sha256 89eb72731903bd32643cf951f474e60de01b61b62b9fa7986c98179105dc0684).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_WeierstrassZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z)) := by
  revert τ z hz
  exact @_root_.P2MW.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.solution
