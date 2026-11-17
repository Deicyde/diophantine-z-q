/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd (git blob 8debe107460fee9fcc2f791b609236f31e9e8faf, sha256 74d6065e9e9b650cc83c6162867a0b9168e2cd24e943c17496ca98cec8f80876).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
    (L : ℕ) [NeZero L] (χ : DirichletCharacter ℂ L) (hχ : χ.IsPrimitive) (hodd : χ.Odd) :
    ∃ E : ModularForm (Gamma1 L) 1,
      (∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ τ : UpperHalfPlane,
        E (γ • τ) =
          χ ((γ 1 1 : ℤ) : ZMod L) *
            ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ (1 : ℤ) * E τ)) ∧
      ModularFormClass.qCoeff E 0 =
        -(∑ a ∈ Finset.range L, (a : ℂ) * χ (a : ZMod L)) / (2 * L) ∧
      ∀ n : ℕ, 0 < n → ModularFormClass.qCoeff E n = ∑ d ∈ n.divisors, χ (d : ZMod L) := by
  revert L χ hχ hodd
  exact @_root_.P2MW.S_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd.solution
