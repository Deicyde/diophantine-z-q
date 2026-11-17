/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul (git blob 58a5176466da748f41f7beff02443799daf5d56a, sha256 4aad8837022281cc31fdbdb12ba63c008e99ded345e12e863f15bc70381ec431).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul

set_option autoImplicit false

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem solution {M : ℕ} {k : ℤ}
    {ε : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.HasNebentypus ε g) {d : ℕ} (hd : Nat.Coprime d M) :
    CuspForm.diamondLinOne M k d g = ε (d : ZMod M) • g := by
  obtain ⟨γ, hγ⟩ := CuspForm.exists_isDiamondLift_of_coprime hd
  refine CuspForm.ext fun τ => ?_
  rw [CuspForm.diamondLinOne_apply_apply hγ, CuspForm.IsGLPos.smul_apply, smul_eq_mul]

  have hs : ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ
      = g (γ • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) :=
    ModularForm.SL_slash_apply (f := ⇑g) (k := k) γ τ
  rw [hs, hg γ hγ.1 τ, hγ.2]
  have hden : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [ModularGroup.denom_apply]
  have hne : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact denom_ne_zero _ τ
  rw [hden, zpow_neg, mul_assoc, mul_comm (_ ^ k * g τ), ← mul_assoc ((_) ^ k)⁻¹, inv_mul_cancel₀
    (zpow_ne_zero k hne), one_mul]
