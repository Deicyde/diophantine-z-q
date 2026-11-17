/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift (git blob fb4a7a49b1720f443949edf8cff1d3def7bb3d3e, sha256 079402eb055b2f410fffa4153ebf6f8cb2a448538b11d466b99a884078ddd554).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne

theorem LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift
    {n : ℕ} (f : ℍ → ℂ)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    IsBoundedOnSiegelWindows ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  revert n f C hC
  exact @_root_.P2MW.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift.solution
