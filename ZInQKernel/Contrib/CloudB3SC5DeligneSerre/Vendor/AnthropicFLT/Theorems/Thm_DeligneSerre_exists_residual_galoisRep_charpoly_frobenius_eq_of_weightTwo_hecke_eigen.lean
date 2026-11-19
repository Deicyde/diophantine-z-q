/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen (git blob 879fa6bf4a7c7879ff133cbfcc784575910671f8, sha256 c188aae759ee295e16b4b641f9e063712ddde214a7065f35c68519fd63b696da).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Residual
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Deformations_MatrixRepresentation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open CongruenceSubgroup Polynomial
open scoped MatrixGroups



theorem DeligneSerre.exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N)
    (g : CuspForm (Gamma1 N) 2) (hg : g ≠ 0) (hεg : CuspForm.HasNebentypus ε g)
    (b : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n)
    (S : Finset ℕ) (R : Subalgebra ℤ ℂ)
    (hR : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S → b p ∈ R) (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ ∧
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N), (p : κ) ≠ 0 →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρ σ = 1) ∧
          ∀ (hpS : p ∉ S) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), A.IsFrobeniusAt σ p →
            ((ρ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).charpoly =
              X ^ 2 - C (φ ⟨b p, hR p hp hpN hpS⟩) * X +
                C (φ ⟨ε (p : ZMod N), hε _⟩ * (p : κ)) := by
  revert N ε g hg hεg b hT S R hR hε κ φ
  exact @_root_.P2MW.S_DeligneSerre_exists_residual_galoisRep_charpoly_frobenius_eq_of_weightTwo_hecke_eigen.solution
