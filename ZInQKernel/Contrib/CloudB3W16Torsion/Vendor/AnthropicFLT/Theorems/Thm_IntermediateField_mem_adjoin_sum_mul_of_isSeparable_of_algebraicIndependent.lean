/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent

set_option backward.isDefEq.respectTransparency true

set_option autoImplicit false

universe u v

theorem IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent
    {k : Type u} {K : Type v} [Field k] [Infinite k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG)
    (hsc : ∀ θ : K, IsSeparable k θ → θ ∈ (⊥ : IntermediateField k K))
    {n : ℕ} (g : Fin (n + 1) → K) (c : Fin (n + 1) → k)
    (x : Fin (n + 1) → FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hx : ∀ i, x i = algebraMap (MvPolynomial (Fin (n + 1)) K) _ (MvPolynomial.X i))
    (hind : AlgebraicIndependent k
      (Fin.snoc (Fin.snoc x (∑ i, algebraMap K _ (g i) * x i)) (algebraMap K _ (∑ i, c i • g i))))
    (θ : FractionRing (MvPolynomial (Fin (n + 1)) K))
    (hθ : IsSeparable
      (IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i})) θ) :
    θ ∈ IntermediateField.adjoin k (Set.range x ∪ {∑ i, algebraMap K _ (g i) * x i}) := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.solution
