/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (git blob c14fd66f2430757352a7725bfe7038dd79c14eab, sha256 01818947c44b9bafd1ea8b8f82c0cc913fc2d50c9409126f0f7c71545aa9cbf3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

universe u in

theorem ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, ModularCurve.IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(B c) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type u) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 +
                6 * (ModularCurve.toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (ModularCurve.tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • ModularCurve.intSeriesC K (d c) := by
  revert M
  exact @_root_.P2MW.S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.solution
