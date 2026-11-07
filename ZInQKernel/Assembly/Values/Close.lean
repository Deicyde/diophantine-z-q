import ZInQKernel.Assembly.Values.Gadgets
import ZInQKernel.Assembly.Values.SignedEncode

/-!
# Semantics of the coordinate window

Blueprint: `assembly/value-templates/close-coordinates-semantics.md`.

`Rel_{value.close_coordinates}(A, L, J, t)` holds exactly when `A = ι(a)`, `L = ι(l)`,
`J = ι(j)` with `a, l ≠ 0` and `|t - r(a, j)| < ε_l`, where `r(a, j) = rRatio a j` is the
rational part of `z_j / z_a` (`z₀ = 0`) and `ε_l = epsIdx l = |u_l| + |v_l|`.
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation Compiler.Precision

/-- The call atom of `value.abs`. -/
theorem lift_abs_call (y : ℕ → ℚ) (x a : Poly) (w : ℕ) :
    (Formula.call absTemplate ![x, a] w).Lift y ↔ ev y a = |ev y x| := by
  refine (Formula.lift_call _ _ _ _).trans ?_
  show absTemplate.Rel (fun k : Fin 2 => ev y (![x, a] k)) ↔ _
  rw [absTemplate_rel_iff]
  rfl

/-- A rational times a sum of four squares equal to `1` is positive. -/
theorem pos_of_mul_four_squares {s a b c d : ℚ} (h : s * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) = 1) :
    0 < s := by
  by_contra hs
  push Not at hs
  have : s * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hs (by positivity)
  linarith

/-- Three parameter points and a scalar determine the sixteen parameters. -/
theorem params_of_points₃ {y : ℕ → ℚ} {A L J : Fin 5 → ℚ} {t : ℚ}
    (h0 : evCode y (varPoint 0) = A) (h5 : evCode y (varPoint 5) = L)
    (h10 : evCode y (varPoint 10) = J) (ht : y 15 = t) :
    ∀ i : Fin 16, y i = Fin.append (Fin.append (Fin.append A L) J) ![t] i := by
  intro i
  refine Fin.addCases (m := 15) (n := 1) (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    refine Fin.addCases (m := 10) (n := 5) (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]
      refine Fin.addCases (m := 5) (n := 5) (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left, ← h0, evCode_varPoint]; simp
      · rw [Fin.append_right, ← h5, evCode_varPoint]; simp [Nat.add_comm]
    · rw [Fin.append_right, ← h10, evCode_varPoint]; simp [Nat.add_comm]
  · rw [Fin.append_right]
    fin_cases i
    simpa using ht

/-- **Semantics of the coordinate window.** -/
theorem closeCoordinates_rel_iff (A L J : Fin 5 → ℚ) (t : ℚ) :
    closeTemplate.Rel (Fin.append (Fin.append (Fin.append A L) J) ![t]) ↔
      ∃ a l j : ℤ, A = iota a ∧ L = iota l ∧ J = iota j ∧ a ≠ 0 ∧ l ≠ 0 ∧
        |t - rRatio a j| < epsIdx l := by
  rw [closeTemplate_rel_iff]
  simp only [closeFormula, Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, lift_member_call, lift_fin, lift_zFormula, lift_divFormula,
    lift_abs_call, lift_nzFormula, lift_posFormula]
  constructor
  · rintro ⟨y, hy, hmA, hmL, hmJ, hfA, hfL, hzA, hzL, hzJ, hdiv, hab0, hab1, hnz, hab2, hpos⟩
    have hA : evCode y (varPoint 0) = A := by
      rw [evCode_varPoint]; funext i; rw [hy ⟨0 + i, by omega⟩]; fin_cases i <;> rfl
    have hL : evCode y (varPoint 5) = L := by
      rw [evCode_varPoint]; funext i; rw [hy ⟨5 + i, by omega⟩]; fin_cases i <;> rfl
    have hJ : evCode y (varPoint 10) = J := by
      rw [evCode_varPoint]; funext i; rw [hy ⟨10 + i, by omega⟩]; fin_cases i <;> rfl
    have ht : y 15 = t := (hy ⟨15, by omega⟩).trans rfl
    obtain ⟨a, ha⟩ := (rel_member_iff_iota _).1 hmA
    obtain ⟨l, hl⟩ := (rel_member_iff_iota _).1 hmL
    obtain ⟨j, hj⟩ := (rel_member_iff_iota _).1 hmJ
    have ha0 : a ≠ 0 := (iota_apply_zero_eq_zero_iff a).1 (by rw [← ha]; exact hfA)
    have hl0 : l ≠ 0 := (iota_apply_zero_eq_zero_iff l).1 (by rw [← hl]; exact hfL)
    have zA := ((holds_zFormula_iota ha).1 hzA).1
    have zL := ((holds_zFormula_iota hl).1 hzL).1
    have zJ := ((holds_zFormula_iota hj).1 hzJ).1
    have hq := ((holds_divFormula_iff _ _ _ _ _).1 hdiv).2
    rw [zA, zJ] at hq
    refine ⟨a, l, j, hA ▸ ha, hL ▸ hl, hJ ▸ hj, ha0, hl0, ?_⟩
    have h0 : y 25 = |(zIdx l).re| := by rw [← zL]; simpa [varPair] using hab0
    have h1 : y 26 = |(zIdx l).im| := by rw [← zL]; simpa [varPair] using hab1
    have h2 : y 27 = |t - rRatio a j| := by
      rw [rRatio, ← hq, ← ht]; simpa [varPair] using hab2
    rw [holds_posFormula] at hpos
    have hp := pos_of_mul_four_squares hpos
    rw [epsIdx]
    simp only [map_sub, map_add, ev_X] at hp
    linarith
  · rintro ⟨a, l, j, rfl, rfl, rfl, ha0, hl0, hw⟩
    set Q := zIdx j / zIdx a with hQ
    have hza : zIdx a ≠ 0 := zIdx_ne_zero (admissible_of_ne_zero ha0)
    have hzl : zIdx l ≠ 0 := zIdx_ne_zero (admissible_of_ne_zero hl0)
    have heps := epsIdx_pos (admissible_of_ne_zero hl0)
    have hs : 0 < |(zIdx l).re| + |(zIdx l).im| - |t - Q.re| := by
      rw [rRatio, ← hQ] at hw; rw [epsIdx] at heps hw; linarith
    obtain ⟨z, hz⟩ := (pos_iff_four_squares _).1 hs
    let pts : List (ℕ × (Fin 5 → ℚ)) := [(0, iota a), (5, iota l), (10, iota j)]
    let vals : List (ℕ × ℚ) := [(15, t), (16, (zIdx a).re), (17, (zIdx a).im),
      (18, (zIdx l).re), (19, (zIdx l).im), (20, (zIdx j).re), (21, (zIdx j).im), (22, Q.re),
      (23, Q.im), (24, ((zIdx a).re ^ 2 - 2 * (zIdx a).im ^ 2)⁻¹), (25, |(zIdx l).re|),
      (26, |(zIdx l).im|), (27, |t - Q.re|), (28, z 0), (29, z 1), (30, z 2), (31, z 3),
      (53, (codeNormY (iota a))⁻¹), (54, (codeNormY (iota l))⁻¹), (55, (codeNormY (iota j))⁻¹),
      (64, (|(zIdx l).re| + |(zIdx l).im|)⁻¹)]
    have hnd : (vals.map Prod.fst).Nodup := by
      rw [show vals.map Prod.fst = [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
        31, 53, 54, 55, 64] from rfl]
      decide
    have hsep : (pts.map Prod.fst).Pairwise Separated := by
      rw [show pts.map Prod.fst = [0, 5, 10] from rfl]; decide
    let y := writeVals (writePoints (fun _ => 0) pts) vals
    have hv : ∀ r v, (r, v) ∈ vals → y r = v := fun r v h => writeVals_of_mem _ hnd h
    have hp : ∀ r P, (r, P) ∈ pts → evCode y (varPoint r) = P := fun r P h =>
      evCode_writeVals_writePoints _ hsep h (by
        intro e he; simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at h
        simp only [vals, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases h with h | h | h <;> obtain ⟨rfl, -⟩ := Prod.mk.inj h <;>
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    have pA := hp 0 (iota a) (by simp [pts])
    have pL := hp 5 (iota l) (by simp [pts])
    have pJ := hp 10 (iota j) (by simp [pts])
    have vz : ∀ k (w : K0), (k, w.re) ∈ vals → (k + 1, w.im) ∈ vals → Pair.val y (varPair k) = w :=
      fun k w h1 h2 => by rw [val_varPair, hv _ _ h1, hv _ _ h2]
    have zA : Pair.val y (varPair 16) = zIdx a := vz _ _ (by simp [vals]) (by simp [vals])
    have zL : Pair.val y (varPair 18) = zIdx l := vz _ _ (by simp [vals]) (by simp [vals])
    have zJ : Pair.val y (varPair 20) = zIdx j := vz _ _ (by simp [vals]) (by simp [vals])
    have zQ : Pair.val y (varPair 22) = Q := vz _ _ (by simp [vals]) (by simp [vals])
    have zinv : ∀ m : ℤ, ∀ k, (k, (codeNormY (iota m))⁻¹) ∈ vals →
        m ≠ 0 → codeNormY (iota m) * y k = 1 := fun m k h hm => by
      rw [hv _ _ h, mul_inv_cancel₀ (codeNormY_iota_ne_zero hm)]
    have v15 := hv 15 (t) (by simp [vals])
    have v25 := hv 25 (|(zIdx l).re|) (by simp [vals])
    have v26 := hv 26 (|(zIdx l).im|) (by simp [vals])
    have v27 := hv 27 (|t - Q.re|) (by simp [vals])
    refine ⟨y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact params_of_points₃ pA pL pJ v15
    · rw [pA, rel_member_iff_iota]; exact ⟨a, rfl⟩
    · rw [pL, rel_member_iff_iota]; exact ⟨l, rfl⟩
    · rw [pJ, rel_member_iff_iota]; exact ⟨j, rfl⟩
    · have := congrFun pA 0; simp only [evCode] at this
      rw [this]; exact (iota_apply_zero_eq_zero_iff a).2 ha0
    · have := congrFun pL 0; simp only [evCode] at this
      rw [this]; exact (iota_apply_zero_eq_zero_iff l).2 hl0
    · exact (holds_zFormula_iota pA).2 ⟨zA, zinv a 53 (by simp [vals])⟩
    · exact (holds_zFormula_iota pL).2 ⟨zL, zinv l 54 (by simp [vals])⟩
    · exact (holds_zFormula_iota pJ).2 ⟨zJ, zinv j 55 (by simp [vals])⟩
    · refine (holds_divFormula_iff _ _ _ _ _).2 ⟨?_, by rw [zQ, zA, zJ]⟩
      rw [ev_norm_eq, zA, hv 24 (((zIdx a).re ^ 2 - 2 * (zIdx a).im ^ 2)⁻¹) (by simp [vals])]
      exact mul_inv_cancel₀ (pairNorm_ne_zero_of_ne_zero hza)
    · simpa [varPair, ← zL] using v25
    · simpa [varPair, ← zL] using v26
    · simp only [map_add, ev_X]
      rw [v25, v26, hv 64 ((|(zIdx l).re| + |(zIdx l).im|)⁻¹) (by simp [vals])]
      exact mul_inv_cancel₀ (by
        have := epsIdx_pos (admissible_of_ne_zero hl0); rw [epsIdx] at this; positivity)
    · have h22 : y 22 = Q.re := by simpa [val_varPair] using congrArg QuadraticAlgebra.re zQ
      simp only [map_sub, ev_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [v27, v15, h22]
    · rw [holds_posFormula]
      simp only [map_sub, map_add, ev_X]
      rw [v25, v26, v27, hv 28 ((z 0)) (by simp [vals]), hv 29 ((z 1)) (by simp [vals]),
        hv 30 ((z 2)) (by simp [vals]), hv 31 ((z 3)) (by simp [vals])]
      exact hz

end ZInQ.Assembly
