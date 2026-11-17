/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_exists_antisymmWeilPairing (git blob 2c8bd4caedfd8e763b0596847f5673861ae8a0bc, sha256 8832a5be7c4f47973f618697366ba91dac6e944a11867e776c9990db2537e319).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_antisymmWeilPairing (K F : Type*) [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] :
    ∃ e : ℕ → Pic0 K F → Pic0 K F → K,
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1) ∧
      (∀ (n : ℕ) (x x' y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
        e n (x + x') y = e n x y * e n x' y) ∧
      (∀ (n : ℕ) (x y y' : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
        e n x (y + y') = e n x y * e n x y') ∧
      (∀ (n : ℕ) (x : Pic0 K F), 0 < n → (n : ℤ) • x = 0 →
        (∀ y : Pic0 K F, (n : ℤ) • y = 0 → e n x y = 1) → x = 0) ∧
      (∀ (n : ℕ) (y : Pic0 K F), 0 < n → (n : ℤ) • y = 0 →
        (∀ x : Pic0 K F, (n : ℤ) • x = 0 → e n x y = 1) → y = 0) ∧
      (∀ (n m : ℕ) (x y : Pic0 K F), 0 < n → 0 < m →
        ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
        e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m) ∧
      (∀ (n : ℕ) (g : SemilinearAut K F) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y)) ∧
      (∀ (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
        (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
        (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
        (hNψ : NormFormulaAlong K ψ hfinψ)
        (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
        (hNφ : NormFormulaAlong K φ hfinφ)
        (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
          = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y)) ∧
      (∀ (n : ℕ) (x y : Pic0 K F), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
        e n x y * e n y x = 1) := by
  revert K F hfg
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_antisymmWeilPairing.solution
