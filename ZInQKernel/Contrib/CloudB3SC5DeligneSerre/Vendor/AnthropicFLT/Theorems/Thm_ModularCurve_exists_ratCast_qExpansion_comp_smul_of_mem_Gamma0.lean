/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 (git blob 1ff574d37da3f741dd231d29f2e69173af2fe01d, sha256 56d32f8d28d184b546b776e61aa4ce32770259a0ac8c57acd6168cd0395e3aca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 (N : ℕ) [NeZero N] (m : ℕ)
    (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by
  revert N m G hG hinv hbd hrat γ hγ n
  exact @_root_.P2MW.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.solution
