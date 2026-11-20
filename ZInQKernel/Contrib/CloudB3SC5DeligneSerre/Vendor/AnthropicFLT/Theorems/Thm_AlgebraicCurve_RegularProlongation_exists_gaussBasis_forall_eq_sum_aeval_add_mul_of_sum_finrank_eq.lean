/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq (git blob fa18ac0e7fcb97c7359a1a101457f134b3fa8953, sha256 3c67b2eda81082f3f8f1b20b9087e2aa6ce3f819e319e84a2a873125c7d4c401).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∃ z : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
      (∀ σ i, z σ ∈ (R i).integers) ∧
      (∀ σ, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z σ ∈ V) ∧
      LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z ∧
      (∀ b : F, (∀ i, b ∈ (R i).integers) →
        ∃ w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F,
          (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            w σ * aeval f q = aeval f p) ∧
          b = ∑ σ, w σ * z σ) ∧
      (∀ (y : F) (w : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
        (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
        (∀ σ, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          w σ * aeval f q = aeval f p) →
        y = ∑ σ, w σ * z σ →
        ∃ (C₁ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → L[X])
          (μ : Fin (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) → F),
          (∀ σ j, (C₁ σ).coeff j ∈ A) ∧
          (∀ σ, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
            ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
            μ σ * aeval f q = aeval f p) ∧
          y = ∑ σ, (aeval f (C₁ σ) + μ σ) * z σ) := by
  revert L A F ι Fb R hR f hf htrL hfd htr heq
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_gaussBasis_forall_eq_sum_aeval_add_mul_of_sum_finrank_eq.solution
