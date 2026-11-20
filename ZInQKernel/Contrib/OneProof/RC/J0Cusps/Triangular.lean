import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! Primitive triangular representatives for the cusp branches. The elementary
matrix reduction is on the spot (c), tex 2937–2939. -/

open Matrix
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.J0Cusps

/-- Reduce the columns of an integral determinant-`N` matrix on the left.
The hypothesis on common divisors is supplied by a primitive bottom row. -/
theorem exists_primitive_triangular (N : ℕ) (hN : 0 < N) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : A.det = N) (hp : ∀ m : ℤ, m ∣ A 1 0 → m ∣ A 1 1 → m ∣ 1) :
    ∃ (a b d : ℕ) (g : SL(2, ℤ)), a * d = N ∧ b < d ∧
      Nat.gcd a (Nat.gcd b d) = 1 ∧
      A = (g : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, d] := by
  let x := A 0 0
  let y := A 1 0
  let a := Int.gcd x y
  have ha : a ≠ 0 := by
    intro ha
    have ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp ha
    rw [Matrix.det_fin_two] at hA
    change x * A 1 1 - A 0 1 * y = _ at hA
    rw [hx, hy] at hA
    norm_num at hA
    omega
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast ha
  let u := Int.gcdA x y
  let v := Int.gcdB x y
  let X := x / (a : ℤ)
  let Y := y / (a : ℤ)
  have hx : X * a = x := Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)
  have hy : Y * a = y := Int.ediv_mul_cancel (Int.gcd_dvd_right _ _)
  have huv : x * u + y * v = a := (Int.gcd_eq_gcd_ab _ _).symm
  have hdet : u * X + v * Y = 1 := by
    apply mul_right_cancel₀ haz
    calc
      (u * X + v * Y) * (a : ℤ) = (X * a) * u + (Y * a) * v := by ring
      _ = 1 * (a : ℤ) := by rw [hx, hy, huv, one_mul]
  let g : SL(2, ℤ) := ⟨!![u, v; -Y, X], by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hdet⟩
  let B := (g : Matrix (Fin 2) (Fin 2) ℤ) * A
  have h00 : B 0 0 = a := by
    change ((!![u, v; -Y, X] : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    change u * x + v * y = a
    linear_combination huv
  have h10 : B 1 0 = 0 := by
    change ((!![u, v; -Y, X] : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0 = _
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    change -Y * x + X * y = 0
    rw [← hx, ← hy]
    ring
  let D := B 1 1
  let E := B 0 1
  have hAD : (a : ℤ) * D = N := by
    have hB : B.det = N := by simp [B, Matrix.det_mul, g.property, hA]
    simpa only [Matrix.det_fin_two, h00, h10, mul_zero, sub_zero] using hB
  have hD : 0 < D := by
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN
    have ha' : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha'.le hn)) (hAD ▸ hN')
  let b := (E % D).toNat
  let d := D.toNat
  have hb : (b : ℤ) = E % D := Int.toNat_of_nonneg (Int.emod_nonneg _ hD.ne')
  have hd : (d : ℤ) = D := Int.toNat_of_nonneg hD.le
  let k : SL(2, ℤ) := ⟨!![1, -(E / D); 0, 1], by norm_num [Matrix.det_fin_two]⟩
  have hB : B = !![(a : ℤ), E; 0, D] := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | exact h00 | exact h10 | rfl
  have hred : (↑k : Matrix (Fin 2) (Fin 2) ℤ) * B = !![(a : ℤ), b; 0, d] := by
    rw [hB]
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · change 1 * (a : ℤ) + -(E / D) * 0 = a
      ring
    · change 1 * E + -(E / D) * D = (b : ℤ)
      rw [hb]
      linear_combination -(Int.emod_add_mul_ediv E D)
    · change 0 * (a : ℤ) + 1 * 0 = 0
      ring
    · change 0 * E + 1 * D = (d : ℤ)
      rw [hd]
      ring
  let G := (k * g)⁻¹
  have hkv : (↑(k * g) : Matrix (Fin 2) (Fin 2) ℤ) * A = !![(a : ℤ), b; 0, d] := by
    change ((↑k : Matrix (Fin 2) (Fin 2) ℤ) * (g : Matrix (Fin 2) (Fin 2) ℤ)) * A = _
    rw [Matrix.mul_assoc]
    exact hred
  have htri : A = (↑G : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, d] := by
    rw [← hkv, ← Matrix.mul_assoc]
    change A = (↑(G * (k * g)) : Matrix (Fin 2) (Fin 2) ℤ) * A
    simp [G]
  refine ⟨a, b, d, G, ?_, ?_, ?_, htri⟩
  · exact_mod_cast (show (a : ℤ) * (d : ℤ) = N by rw [hd, hAD])
  · exact_mod_cast (show (b : ℤ) < (d : ℤ) by rw [hb, hd]; exact Int.emod_lt_of_pos _ hD)
  let m := Nat.gcd a (Nat.gcd b d)
  have hma : (m : ℤ) ∣ (a : ℤ) := by exact_mod_cast Nat.gcd_dvd_left a (Nat.gcd b d)
  have hmb : (m : ℤ) ∣ (b : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_right a (Nat.gcd b d)).trans (Nat.gcd_dvd_left b d)
  have hmd : (m : ℤ) ∣ (d : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_right a (Nat.gcd b d)).trans (Nat.gcd_dvd_right b d)
  have hm0 : (m : ℤ) ∣ A 1 0 := by
    rw [htri]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, add_zero]
    exact dvd_mul_of_dvd_right hma _
  have hm1 : (m : ℤ) ∣ A 1 1 := by
    rw [htri]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact dvd_add (dvd_mul_of_dvd_right hmb _) (dvd_mul_of_dvd_right hmd _)
  have hm : m ∣ 1 := by exact_mod_cast hp _ hm0 hm1
  exact Nat.dvd_one.mp hm


end ZInQ.Manuscript.RC.J0Cusps
