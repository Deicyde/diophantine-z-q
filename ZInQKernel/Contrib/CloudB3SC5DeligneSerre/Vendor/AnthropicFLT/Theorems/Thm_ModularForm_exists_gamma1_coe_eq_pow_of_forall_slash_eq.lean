/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq (git blob 42d2896037608f5767d306109a3ed6ae9370590e, sha256 17123a43cb770adff8958097191068d916537a28e0e9df382415a8548a89a807).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_gamma1_coe_eq_pow_of_forall_slash_eq
    (M : ℕ) [NeZero M] (k : ℤ) (i : ℕ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ P : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * k),
      (∀ t : ZMod M, (⇑(P t) : UpperHalfPlane → ℂ) = (⇑(F t) : UpperHalfPlane → ℂ) ^ i) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(P t) : UpperHalfPlane → ℂ) ∣[(i : ℤ) * k] γ = ⇑(P (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
  revert M k i F hF
  exact @_root_.P2MW.S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq.solution
