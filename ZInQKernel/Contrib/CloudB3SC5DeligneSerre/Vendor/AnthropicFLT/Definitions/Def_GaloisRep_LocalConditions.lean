/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_GaloisRep_LocalConditions (git blob 89822c99384691d1da7e459a65796dfa24d61afa, sha256 7fa8bb9f20822f2ee57bf1ec5209e8a3944a7ebb280e052da10f1f73fa3db371).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def DetIsCyclotomic (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  (p : A) ∈ IsLocalRing.maximalIdeal A ∧
    ∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        LinearMap.det (ρ.ρ σ) - (a : A) ∈ Ideal.span {((p ^ n : ℕ) : A)}

def IsOrdinaryAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)

def IsUnipotentOnInertiaAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ σ) = (Polynomial.X - 1) ^ 2

end GaloisRepAdic

namespace GaloisRep

def ordinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ordinaryCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

end GaloisRep
