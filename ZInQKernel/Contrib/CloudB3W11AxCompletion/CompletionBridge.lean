/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy (AI-assisted)
-/
import ZInQKernel.Contrib.CloudB3W11AxCompletion.AlgebraicDescent

/-!
# The isometric density/completion bridge for Ax–Sen–Tate

The arithmetic input `UniformAxApproximation` is explicitly an unproved
hypothesis in this file. It is a uniform estimate on algebraic elements, not a
restatement of the completed fixed-element theorem: its constant is independent
of the degree of the algebraic approximant. The completion argument below is
proved with the genuine isometric action `PkgI4.cpAct` and the density of
`PadicAlgCl p` in Mathlib's `ℂ_[p]`.

For an arbitrary intermediate field, the conclusion is closure of its actual
image. For a finite intermediate field, `AlgebraicDescent` eliminates that
closure. Nothing here claims to prove the missing arithmetic estimate or to
discharge `HodgeSplit.AxSenTate` unconditionally.
-/

namespace ZInQ.Contrib.CloudB3W11AxCompletion

open ZInQ.Contrib.G9.PkgI4

noncomputable section

/-- In an ultrametric space, an isometry fixing `x` moves an approximant `a`
by no more than its distance from `x`. There is no factor `2`. -/
theorem isometric_displacement_le_of_fixed {X : Type*}
    [PseudoMetricSpace X] [IsUltrametricDist X] {f : X → X}
    (hf : Isometry f) {x : X} (hx : f x = x) (a : X) :
    dist (f a) a ≤ dist a x := by
  have hdist : dist (f a) x = dist a x := by
    calc
      dist (f a) x = dist (f a) (f x) := by rw [hx]
      _ = dist a x := hf.dist_eq a x
  calc
    dist (f a) a ≤ max (dist (f a) x) (dist x a) := dist_triangle_max _ _ _
    _ = dist a x := by rw [hdist, dist_comm x a, max_self]

variable (p : ℕ) [Fact p.Prime]

/-- The repository's completion action is an isometry. -/
theorem cpAct_isometry (σ : GQp p) : Isometry (cpAct p σ) :=
  AddMonoidHomClass.isometry_of_norm (cpAct p σ) (norm_cpAct p σ)

/-- Density of algebraic points in Mathlib's actual completion. -/
theorem exists_algebraic_norm_sub_lt (x : ℂ_[p]) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p]) - x‖ < ε := by
  obtain ⟨a, ha⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  exact ⟨a, by rwa [dist_comm, dist_eq_norm] at ha⟩

/-- The displacement of an algebraic approximant is bounded by its distance
from a point fixed by the genuine completion action. -/
theorem algebraic_displacement_le_of_fixed (σ : GQp p) (x : ℂ_[p])
    (hx : cpAct p σ x = x) (a : PadicAlgCl p) :
    dist (σ a) a ≤ dist (a : ℂ_[p]) x := by
  have h := isometric_displacement_le_of_fixed (cpAct_isometry p σ) hx (a : ℂ_[p])
  rwa [cpAct_coe, UniformSpace.Completion.dist_eq] at h

/-- Norm form of the algebraic displacement bound used by an Ax estimate. -/
theorem algebraic_displacement_norm_le_of_fixed (σ : GQp p) (x : ℂ_[p])
    (hx : cpAct p σ x = x) (a : PadicAlgCl p) :
    ‖σ a - a‖ ≤ ‖(a : ℂ_[p]) - x‖ := by
  simpa only [dist_eq_norm] using algebraic_displacement_le_of_fixed p σ x hx a

/-- Every point in the closure of `K` is fixed by `G_K`. This direction is
unconditional and holds even when `K/ℚ_p` is infinite. -/
theorem cpAct_fixed_of_mem_closure (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : ℂ_[p])
    (hx : x ∈ closure (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p])))) :
    ∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x := by
  intro σ hσ
  have hclosed : IsClosed {z : ℂ_[p] | cpAct p σ z = z} :=
    isClosed_eq (continuous_cpAct p σ) continuous_id
  have hsub : Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p])) ⊆
      {z : ℂ_[p] | cpAct p σ z = z} := by
    rintro z ⟨y, rfl⟩
    simpa only [Set.mem_setOf_eq, fieldToCp_apply] using cpAct_fieldToCp p K y σ hσ
  exact (closure_minimal hsub hclosed) hx

/-- **MISSING ARITHMETIC INPUT — NOT PROVED HERE.**
For this fixed `p,K,C`, whenever every `K`-Galois conjugate moves an algebraic
point `a` by at most a positive radius `δ`, a `K`-point lies within `C * δ` of
`a`. The same `C` must work for all `a : PadicAlgCl p`; it must not depend on
`[K(a):K]` or on a finite normal extension used to contain `a`.

This is an explicit interface for a real uniform Ax estimate. It is not
recorded as a verified printed theorem and is not a new axiom. Allowing `C` to
depend on `a` would not suffice for the completion proof. -/
def UniformAxApproximation (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (C : ℝ) : Prop :=
  ∀ (a : PadicAlgCl p) (δ : ℝ), 0 < δ →
    (∀ σ ∈ K.fixingSubgroup, ‖σ a - a‖ ≤ δ) →
    ∃ b : K, ‖a - (b : PadicAlgCl p)‖ ≤ C * δ

/-- **Conditional completion bridge.** A genuinely uniform algebraic Ax
estimate puts every completed `G_K`-fixed point in the closure of `K`.
No finite-dimensional assumption on `K` is used in this closure statement. -/
theorem mem_closure_of_fixed_of_uniformAxApproximation
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {C : ℝ} (hC : 0 ≤ C)
    (hAx : UniformAxApproximation p K C) (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) :
    x ∈ closure (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p]))) := by
  apply Metric.mem_closure_iff.2
  intro ε hε
  let δ : ℝ := ε / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδid : δ * (C + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  have hδle : δ ≤ ε := by nlinarith [mul_nonneg hC hδ.le]
  have hCδ : C * δ < ε := by nlinarith
  obtain ⟨a, ha⟩ := exists_algebraic_norm_sub_lt p x hδ
  obtain ⟨b, hb⟩ := hAx a δ hδ (fun σ hσ =>
    (algebraic_displacement_norm_le_of_fixed p σ x (hx σ hσ) a).trans ha.le)
  refine ⟨(((b : PadicAlgCl p)) : ℂ_[p]), ⟨b, rfl⟩, ?_⟩
  have hxa : dist x (a : ℂ_[p]) < ε := by
    rw [dist_comm, dist_eq_norm]
    exact ha.trans_le hδle
  have hab : dist (a : ℂ_[p]) (((b : PadicAlgCl p)) : ℂ_[p]) < ε := by
    rw [UniformSpace.Completion.dist_eq, dist_eq_norm]
    exact hb.trans_lt hCδ
  exact (dist_triangle_max x (a : ℂ_[p]) (((b : PadicAlgCl p)) : ℂ_[p])).trans_lt
    (max_lt hxa hab)

/-- With the stated uniform estimate, the closure of an arbitrary `K` is
exactly the completed fixed set. The reverse implication uses no Ax estimate. -/
theorem fixed_iff_mem_closure_of_uniformAxApproximation
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) {C : ℝ} (hC : 0 ≤ C)
    (hAx : UniformAxApproximation p K C) (x : ℂ_[p]) :
    (∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) ↔
      x ∈ closure (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p]))) := by
  exact ⟨mem_closure_of_fixed_of_uniformAxApproximation p K hC hAx x,
    cpAct_fixed_of_mem_closure p K x⟩

/-- **Conditional finite-field descent.** This proves the completion edge,
not the missing uniform arithmetic estimate. -/
theorem exists_field_element_of_fixed_of_uniformAxApproximation
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {C : ℝ} (hC : 0 ≤ C) (hAx : UniformAxApproximation p K C) (x : ℂ_[p])
    (hx : ∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) :
    ∃ y : K, x = (((y : PadicAlgCl p)) : ℂ_[p]) := by
  exact exists_field_element_of_mem_closure p K x
    (mem_closure_of_fixed_of_uniformAxApproximation p K hC hAx x hx)

end

end ZInQ.Contrib.CloudB3W11AxCompletion
