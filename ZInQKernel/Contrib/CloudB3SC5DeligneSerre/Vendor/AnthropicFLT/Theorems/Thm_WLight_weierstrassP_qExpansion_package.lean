/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_weierstrassP_qExpansion_package (git blob cc1436cf1571f46e20ee2aeb0e1d1bea74bda5b8, sha256 1a3f4d686adba0132ff2e9aa5b933ef4a1a36c11696d8abdd445d6f567f57c46).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_weierstrassP_qExpansion_package

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Complex Real
open scoped UpperHalfPlane Manifold

theorem WLight.weierstrassP_qExpansion_package :

    (∀ w : ℂ, 0 < w.im →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m) ∧

    (∀ w : ℂ, w.im < 0 →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m) ∧

    (∀ z τ : ℂ, -τ.im < z.im → z.im < τ.im → z ∈ Complex.integerComplement →
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
        (2 * π * I) ^ 2 *
          (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
            ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
              (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
                cexp (2 * π * I * τ) ^ ((c : ℕ) * m))) ∧

    (∀ L : ℍ → PeriodPair, (∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
      ∀ N a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (∀ τ : ℍ, PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N) =
          (2 * π * I) ^ 2 *
            (cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁ /
                (1 - cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁) ^ 2 +
              1 / 12 +
              ∑' p : ℕ+ × ℕ+, ((p.2 : ℕ) : ℂ) *
                (cexp (2 * π * I / N) ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
                  (cexp (2 * π * I / N))⁻¹ ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
                  2 * cexp (2 * π * I * (τ : ℂ) / N) ^ ((p.1 : ℕ) * N * (p.2 : ℕ))))) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
          (fun τ : ℍ => PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N))) ∧

    (∀ L L' : PeriodPair, ∀ c : ℂ, L'.ω₁ = c * L.ω₁ → L'.ω₂ = c * L.ω₂ →
      ∀ z : ℂ, PeriodPair.weierstrassP L' (c * z) =
        c⁻¹ ^ 2 * PeriodPair.weierstrassP L z) := @_root_.P2MW.S_WLight_weierstrassP_qExpansion_package.solution
