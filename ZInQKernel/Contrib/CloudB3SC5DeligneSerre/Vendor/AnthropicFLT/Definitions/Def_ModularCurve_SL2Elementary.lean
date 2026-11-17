/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_ModularCurve_SL2Elementary (git blob e40b7dabd038906b9041974aba1e52567c517332, sha256 32a4d842842abefeff0db7ed0888ca62295a3b9ddf5e19b8e850f020fe9537b0).
Modified for the Z-in-Q kernel (2026-11-16, cluster C5): import paths relocated (modules already
vendored elsewhere in the kernel are imported from there), the upstream lakefile options set as
`set_option` lines, and: no other change.
Any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.NoncommRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open Matrix MatrixGroups Subgroup

namespace ModularCurve

section Elementary

variable {R : Type*} [CommRing R]

def upperElem (c : R) : SL(2, R) :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

def lowerElem (c : R) : SL(2, R) :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma upperElem_coe (c : R) :
    (upperElem c : Matrix (Fin 2) (Fin 2) R) = !![1, c; 0, 1] := rfl

@[simp] lemma lowerElem_coe (c : R) :
    (lowerElem c : Matrix (Fin 2) (Fin 2) R) = !![1, 0; c, 1] := rfl

lemma upperElem_mul (a b : R) : upperElem a * upperElem b = upperElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

lemma lowerElem_mul (a b : R) : lowerElem a * lowerElem b = lowerElem (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma upperElem_zero : upperElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[simp] lemma lowerElem_zero : lowerElem (0 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma upperElem_pow (a : R) (n : ℕ) : upperElem a ^ n = upperElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, upperElem_mul]
    congr 1
    push_cast
    ring

lemma lowerElem_pow (a : R) (n : ℕ) : lowerElem a ^ n = lowerElem ((n : R) * a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, lowerElem_mul]
    congr 1
    push_cast
    ring

def elemSet (R : Type*) [CommRing R] : Set SL(2, R) :=
  Set.range upperElem ∪ Set.range lowerElem

lemma upperElem_mem_closure_elemSet (c : R) : upperElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inl ⟨c, rfl⟩)

lemma lowerElem_mem_closure_elemSet (c : R) : lowerElem c ∈ closure (elemSet R) :=
  subset_closure (Or.inr ⟨c, rfl⟩)

end Elementary

end ModularCurve
