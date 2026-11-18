import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Lines and right matrix submodules

Tex 9040–9042. The column description and its proof by matrix units are on-the-spot (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LineIndex

open Module

abbrev Vec (K : Type*) := Fin 2 → K
abbrev Mat (K : Type*) := Matrix (Fin 2) (Fin 2) K

variable {K : Type*} [Field K]

/-- The vectors `(0,1)` and `(1,t)` in the two affine charts. -/
def lineVector : Option K → Vec K
  | none => ![0, 1]
  | some t => ![1, t]

private theorem lineVector_ne_zero (L : Option K) : lineVector L ≠ 0 := by
  intro h
  cases L with
  | none => simpa [lineVector] using congrFun h 1
  | some t => simpa [lineVector] using congrFun h 0

/-- The projective line at the given index, as a linear subspace. -/
def line (L : Option K) : Submodule K (Vec K) :=
  Submodule.span K {lineVector L}

/-- The equations of the two charts, in the same coordinates as App F. -/
theorem mem_line_iff (L : Option K) (v : Vec K) :
    v ∈ line L ↔ match L with
      | none => v 0 = 0
      | some t => v 1 = t * v 0 := by
  rw [line, Submodule.mem_span_singleton]
  cases L with
  | none =>
    refine ⟨fun ⟨c, h⟩ => ?_, fun h => ⟨v 1, ?_⟩⟩
    · simpa [lineVector] using (congrFun h 0).symm
    · ext i
      fin_cases i
      · simpa [lineVector] using h.symm
      · simp [lineVector]
  | some t =>
    refine ⟨fun ⟨c, h⟩ => ?_, fun h => ⟨v 0, ?_⟩⟩
    · have h0 : c = v 0 := by simpa [lineVector] using congrFun h 0
      have h1 : c * t = v 1 := by simpa [lineVector] using congrFun h 1
      rw [← h0, ← h1, mul_comm]
    · ext i
      fin_cases i
      · simp [lineVector]
      · simpa [lineVector, mul_comm] using h.symm

/-- Every line has a unique slope or is the vertical line. -/
def lines : Option K ≃ {U : Submodule K (Vec K) // finrank K U = 1} :=
  Equiv.ofBijective (fun L => ⟨line L, finrank_span_singleton (lineVector_ne_zero L)⟩) (by
    constructor
    · intro L T h
      have e : line L = line T := congrArg Subtype.val h
      have hmem : lineVector L ∈ line T := e ▸ Submodule.mem_span_singleton_self _
      have hmem' : lineVector T ∈ line L := e.symm ▸ Submodule.mem_span_singleton_self _
      cases L <;> cases T <;>
        simp_all [mem_line_iff, lineVector]
    · rintro ⟨U, hU⟩
      have hne : U ≠ ⊥ := by
        intro h
        subst U
        simp at hU
      obtain ⟨v, hv, hv0⟩ := U.ne_bot_iff.mp hne
      have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hU hv hv0
      have finish (L : Option K) (hL : v ∈ line L) : ∃ L, (⟨line L,
          finrank_span_singleton (lineVector_ne_zero L)⟩ :
          {W : Submodule K (Vec K) // finrank K W = 1}) = ⟨U, hU⟩ := by
        refine ⟨L, Subtype.ext ?_⟩
        exact (eq_span_singleton_of_mem_of_finrank_eq_one
          (finrank_span_singleton (lineVector_ne_zero L)) hL hv0).trans hspan.symm
      by_cases h0 : v 0 = 0
      · exact finish none ((mem_line_iff _ _).mpr h0)
      · exact finish (some (v 1 / v 0)) ((mem_line_iff _ _).mpr (by
          exact (div_mul_cancel₀ _ h0).symm)))

/-- The subspace of matrices whose columns all belong to `U`. -/
def columns (U : Submodule K (Vec K)) : Submodule K (Mat K) where
  carrier := {M | ∀ j, (fun i => M i j) ∈ U}
  zero_mem' := fun _ => U.zero_mem
  add_mem' hM hN j := U.add_mem (hM j) (hN j)
  smul_mem' c _ hM j := U.smul_mem c (hM j)

/-- Column containment is preserved by right matrix multiplication. -/
theorem columns_mul_mem (U : Submodule K (Vec K)) {M : Mat K}
    (hM : M ∈ columns U) (A : Mat K) : M * A ∈ columns U := by
  intro j
  have h : (fun i => (M * A) i j) = ∑ k : Fin 2, A k j • (fun i => M i k) := by
    funext i
    simp [Matrix.mul_apply, mul_comm]
  rw [h]
  exact U.sum_mem fun k _ => U.smul_mem _ (hM k)

/-- A column space is a product of two copies of the vector subspace. -/
def columnsEquiv (U : Submodule K (Vec K)) : columns U ≃ₗ[K] (Fin 2 → U) where
  toFun M j := ⟨fun i => M.val i j, M.prop j⟩
  invFun v := ⟨fun i j => (v j).val i, fun j => (v j).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_columns (U : Submodule K (Vec K)) :
    finrank K (columns U) = 2 * finrank K U := by
  rw [(columnsEquiv U).finrank_eq, Module.finrank_pi_fintype]
  simp

private def firstColumn : Mat K →ₗ[K] Vec K where
  toFun M i := M i 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every right matrix submodule is the column space of its first-column projection. -/
theorem eq_columns (S : Submodule K (Mat K))
    (hS : ∀ M ∈ S, ∀ A : Mat K, M * A ∈ S) :
    S = columns (S.map firstColumn) := by
  ext M
  constructor
  · intro hM j
    refine ⟨M * Matrix.single j 0 1, hS _ hM _, ?_⟩
    funext i
    exact (Matrix.mul_single_apply_same 1 j 0 i M : _).trans (mul_one _)
  · intro hM
    obtain ⟨A, hA, eA⟩ := hM 0
    obtain ⟨B, hB, eB⟩ := hM 1
    have H : A * Matrix.single 0 0 1 + B * Matrix.single 0 1 1 = M := by
      ext i j
      fin_cases j
      · change (A * (Matrix.single 0 0 1 : Mat K)) i 0 +
          (B * (Matrix.single 0 1 1 : Mat K)) i 0 = M i 0
        rw [Matrix.mul_single_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (by decide),
          add_zero, mul_one]
        exact congrFun eA i
      · change (A * (Matrix.single 0 0 1 : Mat K)) i 1 +
          (B * (Matrix.single 0 1 1 : Mat K)) i 1 = M i 1
        rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ (by decide), Matrix.mul_single_apply_same,
          zero_add, mul_one]
        exact congrFun eB i
    rw [← H]
    exact S.add_mem (hS _ hA _) (hS _ hB _)

/-- The dimension-two submodules of the regular right matrix module. -/
abbrev RightPlanes (K : Type*) [Field K] :=
  {S : Submodule K (Mat K) // (∀ M ∈ S, ∀ A : Mat K, M * A ∈ S) ∧ finrank K S = 2}

private theorem map_firstColumn_columns (U : Submodule K (Vec K)) :
    (columns U).map firstColumn = U := by
  ext v
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact hM 0
  · intro hv
    refine ⟨fun i j => if j = 0 then v i else 0, ?_, ?_⟩
    swap
    · funext i
      change (if (0 : Fin 2) = 0 then v i else 0) = v i
      simp
    intro j
    by_cases h : j = 0
    · simpa only [h, ite_true] using hv
    · change (fun i => if j = 0 then v i else 0) ∈ U
      simp only [ite_eq_right h]
      exact U.zero_mem

/-- Index right planes by the line containing both columns. -/
def rightPlanes : Option K ≃ RightPlanes K :=
  lines.trans (Equiv.ofBijective
    (fun ⟨U, hU⟩ => ⟨columns U, fun _ hM => columns_mul_mem U hM, by simp [finrank_columns, hU]⟩)
    (by
      constructor
      · intro U V h
        apply Subtype.ext
        have e : columns U.val = columns V.val := congrArg Subtype.val h
        simpa only [map_firstColumn_columns] using congrArg (Submodule.map firstColumn) e
      · rintro ⟨S, hS, hdim⟩
        have e := eq_columns S hS
        have h := (congrArg (fun T : Submodule K (Mat K) => finrank K T) e).symm.trans hdim
        rw [finrank_columns] at h
        exact ⟨⟨_, by omega⟩, Subtype.ext e.symm⟩))

end ZInQ.Manuscript.RC.LineIndex

namespace ZInQ.Manuscript.RC.LineIndex

#print axioms lineVector_ne_zero
#print axioms mem_line_iff
#print axioms lines
#print axioms columns_mul_mem
#print axioms columnsEquiv
#print axioms finrank_columns
#print axioms eq_columns
#print axioms map_firstColumn_columns
#print axioms rightPlanes

end ZInQ.Manuscript.RC.LineIndex
