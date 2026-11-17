/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy (AI-assisted)
-/
import ZInQKernel.Contrib.G9.I4Layer

/-!
# Algebraic fixed-element descent and the closed image of a finite p-adic field

These are unconditional supporting results for the Ax–Sen–Tate completion edge.
They use Mathlib's infinite Galois correspondence and finite-dimensional closed
subspace theorem, and the repository's actual Galois action on `ℂ_[p]`.
No uniform Ax approximation estimate is asserted in this file.
-/

namespace ZInQ.Contrib.CloudB3W11AxCompletion

open ZInQ.Contrib.G9.PkgI4

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The actual inclusion of an intermediate field into the completion. -/
def fieldToCp (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp K.val

@[simp]
theorem fieldToCp_apply (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (y : K) :
    fieldToCp p K y = (((y : PadicAlgCl p)) : ℂ_[p]) := rfl

/-- A finite extension of `ℚ_[p]` has closed image in `ℂ_[p]`.
The image is a finite-dimensional `ℚ_[p]`-subspace; no Galois or normality
assumption on the finite extension is needed. -/
theorem isClosed_range_fieldToCp (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    IsClosed (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p]))) := by
  exact (LinearMap.range (fieldToCp p K).toLinearMap).closed_of_finiteDimensional

/-- Eliminate closure of the image of a finite intermediate field. -/
theorem exists_field_element_of_mem_closure
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (x : ℂ_[p])
    (hx : x ∈ closure (Set.range (fun y : K => (((y : PadicAlgCl p)) : ℂ_[p])))) :
    ∃ y : K, x = (((y : PadicAlgCl p)) : ℂ_[p]) := by
  rw [(isClosed_range_fieldToCp p K).closure_eq] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy.symm⟩

/-- Membership in any intermediate field of `ℚ̄_p/ℚ_p` is detected by its
fixing subgroup. This is algebraic descent, not completed descent, and requires
neither finiteness nor normality of the intermediate field. -/
theorem mem_field_iff_fixed (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (a : PadicAlgCl p) :
    a ∈ K ↔ ∀ σ ∈ K.fixingSubgroup, σ a = a := by
  constructor
  · intro ha σ hσ
    exact hσ ⟨a, ha⟩
  · intro ha
    have hmem : a ∈ IntermediateField.fixedField K.fixingSubgroup :=
      (IntermediateField.mem_fixedField_iff K.fixingSubgroup a).2 ha
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at hmem

/-- An algebraic point of `ℂ_p` fixed by `G_K` already belongs to `K`.
Injectivity of the completion inclusion reduces this to infinite Galois theory. -/
theorem algebraic_coe_fixed_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (a : PadicAlgCl p) :
    (∀ σ ∈ K.fixingSubgroup, cpAct p σ (a : ℂ_[p]) = (a : ℂ_[p])) ↔ a ∈ K := by
  rw [mem_field_iff_fixed p K a]
  constructor
  · intro ha σ hσ
    have h := ha σ hσ
    rw [cpAct_coe] at h
    exact (algebraMap (PadicAlgCl p) ℂ_[p]).injective h
  · intro ha σ hσ
    rw [cpAct_coe, ha σ hσ]

/-- Unconditional Ax–Sen–Tate descent for algebraic points only. -/
theorem exists_field_element_of_algebraic_fixed
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (a : PadicAlgCl p)
    (ha : ∀ σ ∈ K.fixingSubgroup, cpAct p σ (a : ℂ_[p]) = (a : ℂ_[p])) :
    ∃ y : K, (a : ℂ_[p]) = (((y : PadicAlgCl p)) : ℂ_[p]) := by
  exact ⟨⟨a, (algebraic_coe_fixed_iff p K a).mp ha⟩, rfl⟩

/-- The image of `K` is fixed by `G_K`, for arbitrary intermediate fields. -/
theorem cpAct_fieldToCp (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (y : K) (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup) :
    cpAct p σ (fieldToCp p K y) = fieldToCp p K y := by
  rw [fieldToCp_apply, cpAct_coe]
  congr 1
  exact hσ y

end

end ZInQ.Contrib.CloudB3W11AxCompletion
