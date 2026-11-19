import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Unipotents

/-! Direct finite check of the ordinary reference for every word at level
divisible by four. The six-line calculation is on-the-spot (c) for the
dyadic reference in tex 8677–8685, 8821–8828 and 8837–8843. -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw Complex CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups

private def stateRow (s : Fin 6) : ZMod 4 × ZMod 4 :=
  ![(0, 1), (2, 1), (1, 0), (1, 1), (1, 2), (1, 3)] s

private def stateS (s : Fin 6) : Fin 6 := ![2, 4, 0, 5, 1, 3] s

private def stateT (s : Fin 6) (n : ZMod 4) : Fin 6 :=
  if s.val < 2 then s else ⟨2 + (((s.val - 2 : ℕ) : ZMod 4) + n).val, by
    have := (((s.val - 2 : ℕ) : ZMod 4) + n).val_lt
    omega⟩

private def stateCoeff (s : Fin 6) (r : ZMod 2) : ℂ :=
  if r = 0 then ![1, 0, 1, 1, 1, 1] s else ![0, 1, 1, I, -1, -I] s

private def stateTable (s : Fin 6) (r : Grid referenceForm) : ℂ :=
  ∏ i, stateCoeff s (r i)

private theorem state_zero : stateTable 0 = referenceWeight := by
  classical
  funext r
  by_cases h : r = 0
  · subst r
    simp [stateTable, stateCoeff, referenceWeight]
  · obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra! hh
      exact h (funext hh)
    rw [referenceWeight, ite_eq_right h, stateTable]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [stateCoeff, hi])

private theorem rowS (s : Fin 6) :
    let r := stateRow s
    let q := stateRow (stateS s)
    (r.2, -r.1) = q ∨ (r.2, -r.1) = (-q.1, -q.2) := by
  fin_cases s <;> decide

private theorem rowT (s : Fin 6) (n : ZMod 4) :
    let r := stateRow s
    let q := stateRow (stateT s n)
    (r.1, r.2 + n * r.1) = q ∨ (r.1, r.2 + n * r.1) = (-q.1, -q.2) := by
  fin_cases s <;> fin_cases n <;> decide

private theorem modTwo_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have hv := r.val_lt
  rcases (show r.val = 0 ∨ r.val = 1 by omega) with h | h
  · exact Or.inl (ZMod.val_injective 2 (by simpa using h))
  · exact Or.inr (ZMod.val_injective 2 (by simpa [ZMod.val_one_eq_one_mod] using h))

private theorem modFour_cases (n : ZMod 4) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by
  have hv := n.val_lt
  rcases (show n.val = 0 ∨ n.val = 1 ∨ n.val = 2 ∨ n.val = 3 by omega) with h | h | h | h
  · exact Or.inl (ZMod.val_injective 4 (by simpa using h))
  · exact Or.inr (Or.inl (ZMod.val_injective 4 (by simpa [ZMod.val_one_eq_one_mod] using h)))
  · exact Or.inr (Or.inr (Or.inl (ZMod.val_injective 4 h)))
  · exact Or.inr (Or.inr (Or.inr (ZMod.val_injective 4 h)))

private theorem char_two : ZMod.stdAddChar (1 : ZMod 2) = -1 := by
  rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp, ZMod.stdAddChar_coe]
  convert Complex.exp_pi_mul_I using 1
  push_cast
  ring

private theorem stateCoeff_S (s : Fin 6) (r : ZMod 2) :
    (∑ t : ZMod 2, stateCoeff s t * ZMod.stdAddChar (-(t * r))) =
      (![1, 1, 2, 1 + I, 2, 1 - I] s) * stateCoeff (stateS s) r := by
  rw [← (ZMod.finEquiv 2).toEquiv.sum_comp (fun t => stateCoeff s t * ZMod.stdAddChar (-(t * r))),
    Fin.sum_univ_two]
  change stateCoeff s 0 * ZMod.stdAddChar (-(0 * r)) +
    stateCoeff s 1 * ZMod.stdAddChar (-(1 * r)) = _
  rcases modTwo_cases r with rfl | rfl <;> fin_cases s <;>
    simp [stateCoeff, stateS, char_two, show -(1 : ZMod 2) = 1 by decide] <;>
    ring_nf <;> simp [I_sq] <;> ring

private theorem stateTable_S (s : Fin 6) :
    ∃ c : ℂ, finiteFourier (stateTable s) = c • stateTable (stateS s) := by
  refine ⟨(∏ i : Fin 3, 1 / (2 * (referenceForm i : ℂ)) ^ (1 / 2 : ℂ)) *
    (∏ _i : Fin 3, (![1, 1, 2, 1 + I, 2, 1 - I] s)), ?_⟩
  funext r
  have he :
      (∑ t : Grid referenceForm, stateTable s t * pairing t r) =
        ∏ i, (∑ t : ZMod 2, stateCoeff s t * ZMod.stdAddChar (-(t * r i))) := by
    simp only [stateTable, pairing, ← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun (i : Fin 3) (t : ZMod 2) =>
      stateCoeff s t * ZMod.stdAddChar (-(t * r i)))).symm
  rw [finiteFourier, he, Pi.smul_apply, smul_eq_mul]
  simp only [stateCoeff_S, Finset.prod_mul_distrib, stateTable, mul_assoc]

private theorem phase_quarter (n : ℤ) :
    kernel (n : ℂ) (1 / 4) = I ^ (n : ZMod 4).val := by
  let j := (n : ZMod 4).val
  have hj : (j : ℤ) + 4 * (n / 4) = n := by
    dsimp [j]
    rw [ZMod.val_intCast]
    exact Int.emod_add_mul_ediv n 4
  have he : 2 * (Real.pi : ℂ) * I * (n : ℂ) * ((1 / 4 : ℝ) : ℂ) =
      (j : ℂ) * ((Real.pi : ℂ) / 2 * I) + ((n / 4 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    have hc := congrArg (fun x : ℤ => (x : ℂ)) hj
    push_cast at hc ⊢
    linear_combination -((Real.pi : ℂ) * I / 2) * hc
  rw [kernel, he, exp_add, exp_int_mul_two_pi_mul_I, mul_one, exp_nat_mul, exp_pi_div_two_mul_I]

private theorem stateCoeff_T (s : Fin 6) (n : ZMod 4) (r : ZMod 2) :
    I ^ (n.val * r.val) * stateCoeff s r =
      ((if s = 1 then I ^ n.val else 1) : ℂ) * stateCoeff (stateT s n) r := by
  rcases modFour_cases n with rfl | rfl | rfl | rfl <;>
    rcases modTwo_cases r with rfl | rfl <;> fin_cases s <;>
    norm_num [stateCoeff, stateT, ZMod.val_add, ZMod.val_natCast, ZMod.val_one_eq_one_mod,
      show (1 : ZMod 2) ≠ 0 by decide] <;>
    simp only [show (2 : ZMod 4).val = 2 by rfl, show (3 : ZMod 4).val = 3 by rfl,
      show (4 : ZMod 4).val = 0 by rfl, show (5 : ZMod 4).val = 1 by rfl,
      show (6 : ZMod 4).val = 2 by rfl] <;>
    norm_num

private theorem stateTable_T (s : Fin 6) (n : ℤ) :
    ∃ c : ℂ, twist n (stateTable s) = c • stateTable (stateT s n) := by
  refine ⟨∏ _i : Fin 3, (if s = 1 then I ^ (n : ZMod 4).val else 1), ?_⟩
  funext r
  have he : kernel (n : ℂ) (energy r) = ∏ i, I ^ ((n : ZMod 4).val * (r i).val) := by
    rw [energy]
    have hf (f : Fin 3 → ℝ) : kernel (n : ℂ) (∑ i, f i) = ∏ i, kernel (n : ℂ) (f i) := by
      simp only [kernel, ← Complex.exp_sum, ofReal_sum, Finset.mul_sum]
    rw [hf]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [offset, referenceForm, Nat.cast_one, mul_one, one_mul]
    have h (j : ℕ) (hj : j < 2) : kernel (n : ℂ) (((j : ℝ) / 2) ^ 2) =
        I ^ ((n : ZMod 4).val * j) := by
      interval_cases j
      · simp [kernel]
      · rw [show ((↑(1 : ℕ) : ℝ) / 2) ^ 2 = 1 / 4 by norm_num, mul_one]
        exact phase_quarter n
    exact h _ (r i).val_lt
  rw [twist, he, Pi.smul_apply, smul_eq_mul, stateTable, ← Finset.prod_mul_distrib]
  simp only [stateCoeff_T, Finset.prod_mul_distrib, stateTable]

private def residueRow (g : SL(2, ℤ)) : ZMod 4 × ZMod 4 :=
  (g.val 1 0, g.val 1 1)

private theorem residueRow_S (g : SL(2, ℤ)) :
    residueRow (g * ModularGroup.S) = ((residueRow g).2, -(residueRow g).1) := by
  simp [residueRow, coe_mul, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]

private theorem residueRow_T (g : SL(2, ℤ)) (n : ℤ) :
    residueRow (g * ModularGroup.T ^ n) =
      ((residueRow g).1, (residueRow g).2 + (n : ZMod 4) * (residueRow g).1) := by
  simp [residueRow, coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, add_comm,
    mul_comm]

private theorem advance (s : Step) (g : SL(2, ℤ)) (q : Fin 6)
    (h : residueRow g = stateRow q ∨ residueRow g = (-(stateRow q).1, -(stateRow q).2)) :
    ∃ t : Fin 6,
      (residueRow (g * s.matrix) = stateRow t ∨
        residueRow (g * s.matrix) = (-(stateRow t).1, -(stateRow t).2)) ∧
      ∃ c : ℂ, wordAction [s] (stateTable q) = c • stateTable t := by
  cases s with
  | inv =>
    refine ⟨stateS q, ?_, stateTable_S q⟩
    rw [Step.matrix, residueRow_S]
    have hq := rowS q
    rcases h with h | h <;> rw [h]
    · exact hq
    · rcases hq with hh | hh
      · right
        exact congrArg (fun r : ZMod 4 × ZMod 4 => (-r.1, -r.2)) hh
      · left
        simpa using congrArg (fun r : ZMod 4 × ZMod 4 => (-r.1, -r.2)) hh
  | trans n =>
    refine ⟨stateT q n, ?_, stateTable_T q n⟩
    rw [Step.matrix, residueRow_T]
    have hq := rowT q n
    rcases h with h | h <;> rw [h]
    · exact hq
    · rcases hq with hh | hh
      · right
        simpa only [Prod.fst, Prod.snd, mul_neg, neg_add_rev, neg_neg, add_comm] using
          congrArg (fun r : ZMod 4 × ZMod 4 => (-r.1, -r.2)) hh
      · left
        simpa only [Prod.fst, Prod.snd, mul_neg, neg_add_rev, neg_neg, add_comm] using
          congrArg (fun r : ZMod 4 × ZMod 4 => (-r.1, -r.2)) hh

private theorem reference_track (l : List Step) (g : SL(2, ℤ)) (q : Fin 6)
    (h : residueRow g = stateRow q ∨ residueRow g = (-(stateRow q).1, -(stateRow q).2)) :
    ∃ t : Fin 6,
      (residueRow (g * wordMatrix l) = stateRow t ∨
        residueRow (g * wordMatrix l) = (-(stateRow t).1, -(stateRow t).2)) ∧
      ∃ c : ℂ, wordAction l (stateTable q) = c • stateTable t := by
  induction l generalizing g q with
  | nil => exact ⟨q, by simpa [wordMatrix], 1, by simp [wordAction]⟩
  | cons s l ih =>
    obtain ⟨t, ht, b, hb⟩ := advance s g q h
    obtain ⟨u, hu, c, hc⟩ := ih (g * s.matrix) t ht
    refine ⟨u, by simpa [wordMatrix, mul_assoc] using hu, b * c, ?_⟩
    change wordAction ([s] ++ l) (stateTable q) = _
    rw [action_append, hb, action_smul, hc, smul_smul]

/-- The reference table itself is an eigenvector for every word of the old
level when the level is divisible by four. The proof uses no Weil index. -/
theorem reference_word {N : ℕ} (hfour : 4 ∣ N) (l : List Step)
    (h : wordMatrix l ∈ Gamma0 N) :
    ∃ c : ℂ, wordAction l referenceWeight = c • referenceWeight := by
  have h₄ := Gamma0_mem.mp (Gamma0_le_Gamma0_of_dvd hfour h)
  obtain ⟨s, hs, c, hc⟩ := reference_track l 1 0 (Or.inl (by decide))
  have hs' : (residueRow (1 * wordMatrix l)).1 = 0 := by simpa [residueRow] using h₄
  have hz : (stateRow s).1 = 0 := by
    rcases hs with h | h
    · exact (congrArg Prod.fst h).symm.trans hs'
    · exact neg_eq_zero.mp ((congrArg Prod.fst h).symm.trans hs')
  have he : s = 0 := by
    have hf (t : Fin 6) : (stateRow t).1 = 0 → t = 0 := by
      fin_cases t <;> decide
    exact hf s hz
  subst s
  exact ⟨c, by simpa only [state_zero] using hc⟩

#print axioms state_zero
#print axioms rowS
#print axioms rowT
#print axioms modTwo_cases
#print axioms modFour_cases
#print axioms char_two
#print axioms stateCoeff_S
#print axioms stateTable_S
#print axioms phase_quarter
#print axioms stateCoeff_T
#print axioms stateTable_T
#print axioms residueRow_S
#print axioms residueRow_T
#print axioms advance
#print axioms reference_track
#print axioms reference_word

end ZInQ.Manuscript.RC.RelativeAction
