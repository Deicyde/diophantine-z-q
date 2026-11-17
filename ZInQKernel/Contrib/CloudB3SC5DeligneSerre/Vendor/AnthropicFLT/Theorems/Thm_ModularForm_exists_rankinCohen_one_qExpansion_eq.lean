/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_rankinCohen_one_qExpansion_eq (git blob 5017fa1ee419cc084af2f578edd56e59e034a02f, sha256 e0dbe8860189e67b4f006d1499cc0d9a3c7dd2be7709c95c58d3bb270e2fc1b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_rankinCohen_one_qExpansion_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane
open scoped MatrixGroups

theorem ModularForm.exists_rankinCohen_one_qExpansion_eq
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    {k₁ k₂ : ℤ} (g : ModularForm Γ k₁) (h : ModularForm Γ k₂) :
    ∃ B : ModularForm Γ (k₁ + k₂ + 2),
      (∀ τ : ℍ, B τ = k₁ * g τ * Derivative.normalizedDerivOfComplex h τ
                     - k₂ * Derivative.normalizedDerivOfComplex g τ * h τ) ∧
      qExpansion 1 (B : ℍ → ℂ) =
        PowerSeries.C (k₁ : ℂ) * qExpansion 1 (g : ℍ → ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (h : ℍ → ℂ)).coeff n)
          - PowerSeries.C (k₂ : ℂ) *
            PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 (g : ℍ → ℂ)).coeff n) *
              qExpansion 1 (h : ℍ → ℂ) := by
  revert Γ h1 k₁ k₂ g h
  exact @_root_.P2MW.S_ModularForm_exists_rankinCohen_one_qExpansion_eq.solution
