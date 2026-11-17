/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le (git blob 9968341d55d7e4f63fdeec605b6125181be23ee7, sha256 2394cd8c7772d78f3c12303367ce4426f20fe0fb0e210a35fb80f992ca191855).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open Polynomial
open scoped MatrixGroups



theorem DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le
    (η : ℝ) (hη : η < 1 / 2) (M : ℕ) (X : Set ℕ)
    (hX : ∀ δ : ℝ, 0 < δ → ∃ s₀ : ℝ, 1 < s₀ ∧ ∀ s : ℝ, 1 < s → s < s₀ →
      ∑' p : {p : ℕ // p.Prime ∧ p ∈ X}, ((p : ℕ) : ℝ) ^ (-s) ≤
        (η + δ) * Real.log (1 / (s - 1))) :
    ∃ A : ℕ, ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) (ZMod ℓ)),
      GaloisFactorsThroughFiniteLevel ρ →
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation →
      ∀ (S : Finset ℕ) (P : Finset (ZMod ℓ)[X]), P.card ≤ M →
        (∀ p : ℕ, p.Prime → p ∉ S →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
            ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p → p ∉ X →
              ((ρ σ : GL (Fin 2) (ZMod ℓ)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).charpoly ∈ P) →
        Nat.card (MonoidHom.range ρ) ≤ A := by
  revert η hη M X hX
  exact @_root_.P2MW.S_DeligneSerre_exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le.solution
