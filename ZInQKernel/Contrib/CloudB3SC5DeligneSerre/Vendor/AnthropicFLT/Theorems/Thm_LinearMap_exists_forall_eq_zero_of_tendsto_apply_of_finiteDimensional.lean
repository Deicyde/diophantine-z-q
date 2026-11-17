/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional (git blob 50f04fec35a7abe221d0519fc4d98dc4088b6201, sha256 912a525b07d8dd7faaa41783fe8ef4f70b468632219f4ec00409d88ec86f00d9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0 := by
  revert X Y T hT
  exact @_root_.P2MW.S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional.solution
