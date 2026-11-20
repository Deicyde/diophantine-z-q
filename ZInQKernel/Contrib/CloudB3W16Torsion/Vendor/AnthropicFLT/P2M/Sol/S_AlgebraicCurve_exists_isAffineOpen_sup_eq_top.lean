/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_isAffineOpen_sup_eq_top. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_isAffineOpen_sup_eq_top

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (haff : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) :
    ∃ U V : C.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ IsAffineOpen (U ⊓ V) ∧ U ⊔ V = ⊤ := by
  classical

  haveI : C.IsSeparated := ⟨by
    rw [show terminal.from C = c ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩

  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨U, hU, hxU⟩ := haff {x}
  have hUne : (U : Set C).Nonempty := ⟨x, hxU x (Finset.mem_singleton_self x)⟩

  have hfin : ((U : Set C)ᶜ).Finite := AlgebraicCurve.finite_compl_of_isOpen c U hUne
  obtain ⟨V, hV, hFV⟩ := haff hfin.toFinset
  refine ⟨U, V, hU, hV, hU.inf hV, ?_⟩
  refine top_le_iff.mp fun y _ => ?_
  by_cases hy : y ∈ U
  · exact Or.inl hy
  · exact Or.inr (hFV y (hfin.mem_toFinset.mpr hy))
