/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range (git blob 94c4a8ed9d746427729bcff1f6e1088e0dcf8d06, sha256 9b8820f5e9b93a9ab4dd2dc869e0eedb5636f369afc4972513dddd4731d1f63b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open Polynomial



theorem GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
    (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) Ω) (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ)
    (hfrob : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
          Matrix.trace ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
            Matrix.det ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ₀ ∧
      (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
      (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ σ = 1 → ρ₀ σ = 1) ∧
      ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).charpoly := by
  revert κ Ω ι ρ hρ S hfrob
  exact @_root_.P2MW.S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.solution
