/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

open TensorProduct nonZeroDivisors

theorem Module.Flat.mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing B]
    [Module.Flat A B] (g : B)
    (hg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra A K],
      (g ⊗ₜ[A] (1 : K)) ∈ nonZeroDivisors (B ⊗[A] K)) :
    g ∈ nonZeroDivisors B ∧ Module.Flat A (B ⧸ Ideal.span {g}) := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_mem_nonZeroDivisors_and_flat_quotient_span_of_forall_isAlgClosed.solution
