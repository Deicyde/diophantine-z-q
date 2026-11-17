/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq (git blob 4be731d8e4316ddbeb8f2a8111a6c4d89cd98603, sha256 f628236a2ae49cb23450db3bae3bfd8b5bcead9d7dcaa68172e8e4258d781695).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gammaH_coe_eq_sum_of_forall_slash_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) [Fintype H] (k : ℤ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ V : ZMod M → ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k,
      (∀ t : ZMod M, (⇑(V t) : UpperHalfPlane → ℂ) =
        ∑ h : H, (⇑(F (t * ((h : (ZMod M)ˣ) : ZMod M))) : UpperHalfPlane → ℂ)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(V t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(V (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
  revert M H k F hF
  exact @_root_.P2MW.S_ModularForm_exists_gammaH_coe_eq_sum_of_forall_slash_eq.solution
