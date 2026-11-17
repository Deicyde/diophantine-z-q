/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

theorem LinearMap.nonempty_kerModRange_equiv_of_equiv_comm
    {R : Type u} [CommRing R] {C C' : ℕ → Type u}
    [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, AddCommGroup (C' i)] [∀ i, Module R (C' i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (d' : ∀ i, C' i →ₗ[R] C' (i + 1))
    (e : ∀ i, C i ≃ₗ[R] C' i) (he : ∀ i x, e (i + 1) (d i x) = d' i (e i x)) :
    Nonempty (LinearMap.ker (d 0) ≃ₗ[R] LinearMap.ker (d' 0)) ∧
    ∀ i, Nonempty
      ((LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) ≃ₗ[R]
       (LinearMap.ker (d' (i + 1)) ⧸ (LinearMap.range (d' i)).comap (LinearMap.ker (d' (i + 1))).subtype)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_nonempty_kerModRange_equiv_of_equiv_comm.solution
