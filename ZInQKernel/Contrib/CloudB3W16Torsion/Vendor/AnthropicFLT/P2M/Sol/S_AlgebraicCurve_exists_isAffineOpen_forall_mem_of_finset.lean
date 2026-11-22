/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isAffineOpen_of_maximal_domain
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_transcendental_mem_range_stalk_iff_ne
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_isAffineOpen_forall_mem_of_finset

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial
open AlgebraicGeometry.Polynomial

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (F : Finset C) : ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical

  have hinf := AlgebraicCurve.infinite_setOf_isClosed_singleton c
  obtain ⟨Q, hQ, hQF⟩ := (hinf.diff F.finite_toSet).nonempty
  obtain ⟨Q', hQ', hQ'Q⟩ := (hinf.diff (Set.finite_singleton Q)).nonempty
  simp only [Set.mem_setOf_eq] at hQ hQ'

  obtain ⟨f, hf, hfQ⟩ := AlgebraicCurve.exists_transcendental_mem_range_stalk_iff_ne c Q hQ

  let U : C.Opens := ⟨({Q} : Set C)ᶜ, hQ.isOpen_compl⟩
  have hU_mem : ∀ x : C, x ∈ U ↔ x ≠ Q := fun x => by
    change x ∈ ({Q} : Set C)ᶜ ↔ x ≠ Q
    simp
  haveI : Nonempty U := ⟨⟨Q', (hU_mem Q').mpr (by simpa using hQ'Q)⟩⟩

  have hfU : f ∈ (algebraMap Γ(C, U) C.functionField).range := by
    rw [AlgebraicGeometry.Scheme.Opens.range_algebraMap_functionField_eq_iInf]
    simp only [Subring.mem_iInf]
    exact fun x hx => (hfQ x).mpr ((hU_mem x).mp hx)
  obtain ⟨s, hs⟩ := hfU
  have hgerm : C.germToFunctionField U s = f := hs
  refine ⟨U, ?_, fun x hx => (hU_mem x).mpr fun h => hQF (h ▸ hx)⟩

  refine AlgebraicCurve.isAffineOpen_of_maximal_domain c U s (fun x hx => ?_) ?_
  · rw [hgerm] at hx
    exact (hU_mem x).mpr ((hfQ x).mp hx)
  · rw [hgerm]
    exact hf
