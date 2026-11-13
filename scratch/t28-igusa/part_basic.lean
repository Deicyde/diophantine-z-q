
section Basic
variable {K : Type*} [Field K]

theorem J2_eq (a : Fin 7 → K) : J2 a = J2R a := rfl
theorem J4_eq (a : Fin 7 → K) : J4 a = J4R a := rfl
theorem J6_eq (a : Fin 7 → K) : J6 a = J6R a := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem J10_eq (a : Fin 7 → K) : J10 a = J10R a := by
  simp only [J10, j10Data, J10R, J10R0, J10R1, J10R2, J10R3, J10R4, J10R5, J10R6, J10R7, J10R8,
    J10R9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_seven]
  norm_num
  ring

open Polynomial in
theorem sexticAct_eq (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (e : K) :
    sexticAct f M e = actC f (M 0 0) (M 0 1) (M 1 0) (M 1 1) e := by
  have key : C e * ∑ k : Fin 7, C (f k) * (C (M 0 0) * X + C (M 0 1)) ^ (k : ℕ) *
      (C (M 1 0) * X + C (M 1 1)) ^ (6 - (k : ℕ)) =
      ∑ i : Fin 7, C (actC f (M 0 0) (M 0 1) (M 1 0) (M 1 1) e i) * X ^ (i : ℕ) := by
    simp only [Fin.sum_univ_seven, actC]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Matrix.cons_val, map_add, map_mul, map_pow,
      map_one, map_ofNat]
    norm_num
    ring
  funext i
  unfold sexticAct
  rw [key, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Fin.val_inj]
  simp

end Basic
