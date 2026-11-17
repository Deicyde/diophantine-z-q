/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

theorem LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
    {k : Type u} [DivisionRing k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.solution
