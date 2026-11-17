/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq (git blob 526d62930f1e943a582fd41b8947faca7c262e65, sha256 8cb0bae05552902e676eb0a943203d5fe1dfb41fb7271e12cc022af945c1f0af).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) [Fintype H] (τ : UpperHalfPlane)
    (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ CongruenceSubgroup.Gamma0 N) (d : ℕ)
    (hd : d = 1 ∨ (d = 2 ∧ (PeriodPair.ofTau τ).g₃ = 0) ∨ (d = 3 ∧ (PeriodPair.ofTau τ).g₂ = 0))
    (hsum : ∀ j : ℕ, 0 < j →
      ∑ h : H, (PeriodPair.ofTau τ).weierstrassP ((((h : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^ (d * j) =
        ∑ h : H, (PeriodPair.ofTau τ).weierstrassP
          ((((CohCarrier.gamma0Units N ⟨γ₀, hγ₀⟩ * (h : (ZMod N)ˣ) : (ZMod N)ˣ) : ZMod N).val : ℂ) / N) ^
            (d * j)) :
    ∃ γ ∈ CohCarrier.GammaH N H, γ • τ = γ₀ • τ := by
  revert N H τ γ₀ hγ₀ d hd hsum
  exact @_root_.P2MW.S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq.solution
