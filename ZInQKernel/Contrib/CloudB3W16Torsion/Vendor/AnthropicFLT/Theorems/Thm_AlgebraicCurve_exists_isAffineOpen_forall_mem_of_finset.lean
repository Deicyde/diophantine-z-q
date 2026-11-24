/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (F : Finset C) : ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset.solution
