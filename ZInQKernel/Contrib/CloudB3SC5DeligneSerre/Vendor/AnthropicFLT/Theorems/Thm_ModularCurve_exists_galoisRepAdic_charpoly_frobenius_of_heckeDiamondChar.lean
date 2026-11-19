/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar (git blob b78b3adb80ec4c2a3da77b936a3aa0ed0c441cbb, sha256 fd70d9f86f39ebef9386c4dd8e58a66bc842a1e9776fb83d29a4fa065b5f6139).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Adic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open Polynomial

theorem ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (i₀ : ℤ_[p] →+* O) (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) →+* K),
      (∀ c : ℤ_[p],
        Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p (ModularCurve.JOne M)) (c : ℚ_[p]))
          = algebraMap O K (i₀ c)) →
      ∃ ρ : GaloisRepAdic O,
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * p → ∀ a d : O,
          Λ (ModularCurve.rationalHeckeOne p (ModularCurve.JOne M) ⟨ℓ, hℓ⟩) = algebraMap O K a →
          Λ (ModularCurve.rationalDiamondOne p (ModularCurve.JOne M) ℓ) * algebraMap O K d = 1 →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
              LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (d * a) * X + C (d * (ℓ : O))) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M * p → ρ.IsUnramifiedAt ℓ) := by
  revert M p O K i₀ hpO
  exact @_root_.P2MW.S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.solution
