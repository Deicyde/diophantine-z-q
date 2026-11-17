/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem (git blob 3719c443391e85b1cbbcc0dca58b3e52eefc8bad, sha256 e36d99e3d6606f926958793c18b6bc32b4cab6dfeb7440527d826727f3fc4a71).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalLanglands_HeckeCosetSystem
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem
    {G : Type*} [Group G] {n : ℕ} {U : Subgroup G} {gv : G}
    {reps reps' : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hsys' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {φ : G → ℂ} (hinv : ∀ g : G, ∀ u ∈ U, φ (g * u) = φ g) (g : G) :
    ∑ i, φ (g * reps' i) = ∑ i, φ (g * reps i) := by
  revert G n U gv reps reps' hsys hsys' φ hinv g
  exact @_root_.P2MW.S_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem.solution
