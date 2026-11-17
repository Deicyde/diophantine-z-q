/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff (git blob 51bf114557b21b66003e7e6e2d0920426aebbdc8, sha256 aead53b9c1efa084f4437002a63cb8dade00685cf5aa33f8bcf642559c6374dd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm Real Matrix

theorem PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff
    (M : ℕ) [NeZero M] :
    ∃ W : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ (L : UpperHalfPlane → PeriodPair),
        (∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : UpperHalfPlane),
          W t τ = 12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(W t) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) := by
  revert M
  exact @_root_.P2MW.S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.solution
