/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen (git blob 07e86257090efd91498ea69fa85993d08b6cb581, sha256 dacd93ba16c0d4455d4e604879e3393c75ff414b317eaa5db63ab07c9fac6b13).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup Polynomial
open scoped MatrixGroups



theorem DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ModularFormClass.qCoeff f p ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (k : Type) [Field k] [Finite k] (φ : R →+* k) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) k, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : k) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
              X ^ 2 - C (φ ⟨ModularFormClass.qCoeff f p, hR p hp hpN⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩) := by
  revert N ε f hf₁ hT R hR hε k φ
  exact @_root_.P2MW.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightOne_hecke_eigen.solution
