import Mathlib

/-!
# Writing points into an assignment

`writePoints x l` overwrites an assignment `x : ℕ → ℚ` with the five coordinates of each point
`(r, P)` of the list `l` at `X_r, …, X_{r+4}` (the first entry covering an index wins). If the
starts of `l` are pairwise at distance at least `5`, every point of `l` is read back unchanged
(`writePoints_point`).
-/

namespace ZInQ.Translation

/-- The point `(x_r, …, x_{r+4})` of an assignment. -/
def pointAt (x : ℕ → ℚ) (r : ℕ) : Fin 5 → ℚ := fun i => x (r + i)

/-- Write the points of `l` into `x`. -/
def writePoints (x : ℕ → ℚ) : List (ℕ × (Fin 5 → ℚ)) → ℕ → ℚ
  | [] => x
  | (r, P) :: l => fun j => if h : r ≤ j ∧ j < r + 5 then P ⟨j - r, by omega⟩ else writePoints x l j

/-- The starts `r, r'` of two points are at distance at least `5`. -/
def Separated (r r' : ℕ) : Prop := r + 5 ≤ r' ∨ r' + 5 ≤ r

instance : DecidableRel Separated := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem writePoints_of_not_mem (x : ℕ → ℚ) (l : List (ℕ × (Fin 5 → ℚ))) {j : ℕ}
    (h : ∀ e ∈ l, ¬ (e.1 ≤ j ∧ j < e.1 + 5)) : writePoints x l j = x j := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨r, P⟩ := e
    simp only [writePoints]
    rw [dite_eq_right (h _ List.mem_cons_self)]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

/-- **Reading back a written point.** -/
theorem writePoints_point (x : ℕ → ℚ) {l : List (ℕ × (Fin 5 → ℚ))}
    (hl : (l.map Prod.fst).Pairwise Separated) {r : ℕ} {P : Fin 5 → ℚ} (h : (r, P) ∈ l) :
    pointAt (writePoints x l) r = P := by
  funext i
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨r', P'⟩ := e
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hl
    simp only [pointAt, writePoints]
    rcases List.mem_cons.1 h with h' | h'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
      rw [dite_eq_left ⟨by omega, by omega⟩]
      congr 1
      ext
      simp
    · have hsep := hl.1 r ⟨(r, P), h', rfl⟩
      rw [dite_eq_right (by unfold Separated at hsep; omega)]
      exact ih hl.2 h'

/-- **Reading back a written point**, for a list whose distinct entries have separated
starts. -/
theorem writePoints_point_of_consistent (x : ℕ → ℚ) {l : List (ℕ × (Fin 5 → ℚ))}
    (hl : l.Pairwise fun e e' => e = e' ∨ Separated e.1 e'.1) {r : ℕ} {P : Fin 5 → ℚ}
    (h : (r, P) ∈ l) : pointAt (writePoints x l) r = P := by
  funext i
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨r', P'⟩ := e
    rw [List.pairwise_cons] at hl
    simp only [pointAt, writePoints]
    by_cases he : (r', P') = (r, P)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [dite_eq_left ⟨by omega, by omega⟩]
      congr 1
      ext
      simp
    · have h' : (r, P) ∈ l := by
        rcases List.mem_cons.1 h with h' | h'
        · exact absurd h'.symm he
        · exact h'
      rcases hl.1 _ h' with h'' | hsep
      · exact absurd h'' he
      · rw [dite_eq_right (by unfold Separated at hsep; simp only at hsep; omega)]
        exact ih hl.2 h'

end ZInQ.Translation
