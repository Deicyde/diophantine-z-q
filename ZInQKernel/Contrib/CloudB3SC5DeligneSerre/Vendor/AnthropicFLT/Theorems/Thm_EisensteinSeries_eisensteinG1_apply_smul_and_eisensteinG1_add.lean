/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add (git blob 32c5a1cae0f18a2217dbbc71975cc4ca0b189bef, sha256 afb48b11b0dba9f2affc12d62895edcc86a60e85e74352f80a702cd01e837b5f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_WeierstrassZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real MatrixGroups Matrix

theorem EisensteinSeries.eisensteinG1_apply_smul_and_eisensteinG1_add (N : ℕ) [NeZero N]
    (τ : UpperHalfPlane) :
    (∀ (γ : SL(2, ℤ)) (v : Fin 2 → ℤ),
        EisensteinSeries.eisensteinG1 N v (γ • τ) =
          UpperHalfPlane.denom γ τ *
            EisensteinSeries.eisensteinG1 N (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) τ) ∧
    (∀ v w : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        EisensteinSeries.eisensteinG1 N (v + (N : ℤ) • w) τ =
          EisensteinSeries.eisensteinG1 N v τ) := by
  revert N τ
  exact @_root_.P2MW.S_EisensteinSeries_eisensteinG1_apply_smul_and_eisensteinG1_add.solution
