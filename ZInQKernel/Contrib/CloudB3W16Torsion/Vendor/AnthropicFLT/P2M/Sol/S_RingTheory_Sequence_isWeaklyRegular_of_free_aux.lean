/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_RingTheory_Sequence_isWeaklyRegular_of_free_aux. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_isSMulRegular_iff_of_free
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_RingTheory_Sequence_isWeaklyRegular_of_free_aux

open scoped Pointwise TensorProduct

theorem solution.{u, v} {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · haveI : Subsingleton ((R ⧸ Ideal.span {x}) ⊗[R] M) := Module.subsingleton (R ⧸ Ideal.span {x}) _
      exact iff_of_true
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact IH (by simp_all)
