/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
    (K : Type u) (L : Type v) (Ω : Type w) [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime := by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range.solution
