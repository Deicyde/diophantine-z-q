/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt

set_option autoImplicit false

namespace AlgebraicCurve
export AlgebraicCurve (Place Divisor IsCurveOver LSpace RiemannGenusReachedAt lSpaceOn exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt Place.exists_forall_adicValuation_sub_eq)
open AlgebraicCurve
open WithZero

theorem exists_mem_lSpaceOn_adicValuation_eq' {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (S : Set (Place K F)) {v₀ : Place K F} (hv₀ : v₀ ∉ S) (D : Divisor K F) (v : Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v) := by
  classical

  obtain ⟨a, ha⟩ := Place.exists_forall_adicValuation_sub_eq ({v} : Finset (Place K F)) (fun _ => (0 : F)) (fun _ => D v)
  have hav : v.adicValuation a = exp (D v) := by
    have := ha v (Finset.mem_singleton_self v)
    rwa [sub_zero] at this

  let α : Place K F → F := fun w => if w = v then a else 0
  let E : Divisor K F := D - Finsupp.single v 1
  have hα : {w | w ∈ S ∧ ¬ w.adicValuation (α w) ≤ exp (E w)}.Finite := by
    apply (Set.finite_singleton v).subset
    rintro w ⟨-, hw⟩
    by_contra hwv
    apply hw
    have hαw : α w = 0 := if_neg hwv
    rw [hαw, Valuation.map_zero]
    exact zero_le'
  obtain ⟨f, hf⟩ := exists_forall_adicValuation_sub_le_of_riemannGenusReachedAt h S hv₀ E α hα
  have hEv : E v = D v - 1 := by simp [E]
  have hEw : ∀ w, w ≠ v → E w = D w := fun w hw => by
    rw [show E w = D w - Finsupp.single v (1 : ℤ) w from rfl, Finsupp.single_apply, if_neg (fun h => hw h.symm),
      sub_zero]
  have hfv : v.adicValuation (a - f) < v.adicValuation a := by
    have := hf v hv
    simp only [α, if_pos rfl, hEv] at this
    rw [hav]
    exact lt_of_le_of_lt this (exp_lt_exp.mpr (by omega))
  have hfval : v.adicValuation f = exp (D v) := by
    rw [← hav, show f = a - (a - f) by ring]
    exact Valuation.map_sub_eq_of_lt_left _ hfv
  refine ⟨f, ?_, hfval⟩
  intro w hwS
  by_cases hwv : w = v
  · subst hwv
    exact hfval.le
  · have := hf w hwS
    simp only [α, if_neg hwv, hEw w hwv, zero_sub, Valuation.map_neg] at this
    exact this

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt.AlgebraicCurve in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))]
    {γ : ℤ} {D₀ : AlgebraicCurve.Divisor K F} (h : AlgebraicCurve.RiemannGenusReachedAt γ D₀)
    (S : Set (AlgebraicCurve.Place K F)) {v₀ : AlgebraicCurve.Place K F} (hv₀ : v₀ ∉ S)
    (D : AlgebraicCurve.Divisor K F) (v : AlgebraicCurve.Place K F) (hv : v ∈ S) :
    ∃ f : F, f ∈ AlgebraicCurve.lSpaceOn S D ∧ v.adicValuation f = WithZero.exp (D v) :=
  exists_mem_lSpaceOn_adicValuation_eq' h S hv₀ D v hv
