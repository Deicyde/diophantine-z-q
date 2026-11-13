/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/MeasureTheory/Group/Measure.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import Mathlib.MeasureTheory.Group.Measure

/-!
# Measures invariant under addition

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
    rw [h, measure_preimage_add_right]
  simp_rw [htranslate]
  simp

end TauCeti
