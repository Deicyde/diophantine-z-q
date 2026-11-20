/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicBox_exists_denom_of_hasCompactSupport (git blob c3ca9208db643e431a2f67d7b1ff9f0bb2324e21, sha256 a97ef61bbd227bf3e3b39e35bc493a0cd6fb3b56b4e65c854a796af07151f739).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
theorem NumberField.AdelicBox.exists_denom_of_hasCompactSupport
    {F : Type*} [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ κ : F, h (algebraMap F (FiniteAdeleRing (𝓞 F) F) κ) ≠ 0 →
      ∃ a : 𝓞 F, (d : F) * κ = a := by
  revert F h hcs
  exact @_root_.P2MW.S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.solution
