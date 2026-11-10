import ZInQKernel.RouteK.Rank5b
open ZInQ.RouteK
example : (21).primeFactors = {3, 7} := by
  rw [show (21:ℕ) = 3 * 7 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]; rfl
example : legBit 3 (7:ℕ) = 0 := by
  unfold legBit; rw [if_pos]; exact ⟨1, by decide⟩
example : legBit 7 (3:ℕ) = 1 := by
  unfold legBit; rw [if_neg]; rintro ⟨r, hr⟩; fin_cases r <;> revert hr <;> decide
example : Matrix.det !![(1 : ZMod 2), 0, 1, 1, 0; 0, 1, 0, 1, 1; 1,1,0,0,0; 0,1,0,1,1; 1,0,1,0,1] = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]; decide
