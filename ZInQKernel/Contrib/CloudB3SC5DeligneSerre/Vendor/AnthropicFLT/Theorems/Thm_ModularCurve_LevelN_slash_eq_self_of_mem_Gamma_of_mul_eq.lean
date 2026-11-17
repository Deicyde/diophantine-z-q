/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq (git blob 14de8298d642d9a653ac846d64345c5212b7c5ca, sha256 51f35f0fb8ccdbce2a0c2b2b198c23f946ec2fb86826ec690db06edaf9d6dc11).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem ModularCurve.LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq (N : ℕ) [NeZero N]
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (a b c e : UpperHalfPlane → ℂ) (ha : a ∈ ModularCurve.LevelN.ring N)
    (hb : b ∈ ModularCurve.LevelN.ring N) (hc : c ∈ ModularCurve.LevelN.ring N)
    (he : e ∈ ModularCurve.LevelN.ring N) (hb0 : b ≠ 0) (he0 : e ≠ 0)
    (h : ∀ τ : UpperHalfPlane, F τ * b τ * e τ ^ 2 =
      a τ * (e τ * deriv (c ∘ UpperHalfPlane.ofComplex) τ -
        c τ * deriv (e ∘ UpperHalfPlane.ofComplex) τ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    F ∣[(2 : ℤ)] γ = F := by
  revert N F hF a b c e ha hb hc he hb0 he0 h γ hγ
  exact @_root_.P2MW.S_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq.solution
