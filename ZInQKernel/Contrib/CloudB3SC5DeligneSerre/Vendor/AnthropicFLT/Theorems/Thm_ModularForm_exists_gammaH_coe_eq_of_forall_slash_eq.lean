/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq (git blob f19ed23d8e38a534ba9717e536553fc0c0a0b128, sha256 bf9f2d0a9a86aa05ede3541c0536c58e023d245643f34a3437cd82b36eb723f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (g : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ γ ∈ CohCarrier.GammaH M H, (⇑g : UpperHalfPlane → ℂ) ∣[k] γ = ⇑g) :
    ∃ f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  revert M H k g hg
  exact @_root_.P2MW.S_ModularForm_exists_gammaH_coe_eq_of_forall_slash_eq.solution
