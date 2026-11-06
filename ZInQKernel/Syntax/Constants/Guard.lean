import ZInQKernel.Model.Field.Codes

/-!
# The finite false-triple product

Blueprint: `syntax/constants/guard-product.md`.

For an integer `T`, the false triples in the box are the `(a, b, c) ∈ [-T, T]³` with `ab ≠ c`
(`falseTriples T`; empty for `T < 0`). For such a triple, the fifteen coordinates of
`(ι(a), ι(b), ι(c))` in point-major order are `tripleCode (a, b, c) : Fin 15 → ℚ`; writing them
as reduced fractions `A_j / B_j`, `D_abc = ∏_j B_j` (`tripleDen`). The guard polynomial is
`G_T = ∏_{false triples} ∑_j (D_abc X_j - (D_abc / B_j) A_j)²  ∈ ℤ[X_1, …, X_15]`
(`guardPoly T`, empty product `1`). It is never expanded.

We prove that `B_j ∣ D_abc`, and that the rational zero set of `G_T` is exactly the set of
codes `tripleCode (a, b, c)` of the false triples (`guardPoly_eval_eq_zero_iff`).
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- The box `[-T, T]³`. -/
def guardBox (T : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  Finset.Icc (-T) T ×ˢ Finset.Icc (-T) T ×ˢ Finset.Icc (-T) T

/-- The false triples in the box: `(a, b, c) ∈ [-T, T]³` with `ab ≠ c`. -/
def falseTriples (T : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (guardBox T).filter fun t => t.1 * t.2.1 ≠ t.2.2

theorem mem_falseTriples {T a b c : ℤ} :
    (a, b, c) ∈ falseTriples T ↔ |a| ≤ T ∧ |b| ≤ T ∧ |c| ≤ T ∧ a * b ≠ c := by
  simp only [falseTriples, guardBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    abs_le, and_assoc]

/-- The fifteen coordinates of `(ι(a), ι(b), ι(c))` in point-major order: coordinate `j` is
coordinate `j % 5` of the point `j / 5`. -/
noncomputable def tripleCode (t : ℤ × ℤ × ℤ) : Fin 15 → ℚ := fun j =>
  iota (![t.1, t.2.1, t.2.2] ⟨j / 5, by omega⟩) ⟨j % 5, by omega⟩

/-- Coordinate `5 i + k` of the triple code is coordinate `k` of the `i`-th point. -/
theorem tripleCode_apply (a b c : ℤ) (i : Fin 3) (k : Fin 5) :
    tripleCode (a, b, c) ⟨5 * i + k, by omega⟩ = iota (![a, b, c] i) k := by
  have h₁ : (⟨(5 * i.val + k.val) / 5, by omega⟩ : Fin 3) = i := Fin.ext (by simp only; omega)
  have h₂ : (⟨(5 * i.val + k.val) % 5, by omega⟩ : Fin 5) = k := Fin.ext (by simp only; omega)
  simp only [tripleCode]
  rw [h₁, h₂]

/-- Two triple codes agree iff the three codes agree. -/
theorem tripleCode_eq_iff {t : ℤ × ℤ × ℤ} {x : Fin 15 → ℚ} :
    x = tripleCode t ↔ ∀ (i : Fin 3) (k : Fin 5),
      x ⟨5 * i + k, by omega⟩ = iota (![t.1, t.2.1, t.2.2] i) k := by
  obtain ⟨a, b, c⟩ := t
  refine ⟨fun h i k => by rw [h, tripleCode_apply], fun h => funext fun j => ?_⟩
  have hj : (⟨5 * (⟨j / 5, by omega⟩ : Fin 3) + (⟨j % 5, by omega⟩ : Fin 5), by omega⟩ : Fin 15)
      = j := Fin.ext (by simp only; omega)
  rw [← hj, h, tripleCode_apply]

/- From here on the codes are only used through the lemmas above. -/
attribute [irreducible] tripleCode

/-- `D_abc = ∏_j B_j`, the product of the reduced denominators of the fifteen coordinates. -/
noncomputable def tripleDen (t : ℤ × ℤ × ℤ) : ℕ := ∏ j, (tripleCode t j).den

theorem tripleDen_pos (t : ℤ × ℤ × ℤ) : 0 < tripleDen t :=
  Finset.prod_pos fun j _ => (tripleCode t j).den_pos

/-- `B_j ∣ D_abc`, so each factor has integer coefficients. -/
theorem den_dvd_tripleDen (t : ℤ × ℤ × ℤ) (j : Fin 15) : (tripleCode t j).den ∣ tripleDen t := by
  unfold tripleDen
  exact Finset.dvd_prod_of_mem (fun j => (tripleCode t j).den) (Finset.mem_univ j)

/-- The factor `∑_j (D_abc X_j - (D_abc / B_j) A_j)²` of a triple. -/
noncomputable def guardFactor (t : ℤ × ℤ × ℤ) : MvPolynomial (Fin 15) ℤ :=
  ∑ j, (C (tripleDen t : ℤ) * X j -
    C (((tripleDen t / (tripleCode t j).den : ℕ) : ℤ) * (tripleCode t j).num)) ^ 2

/-- The guard polynomial `G_T`: the product of the factors over the false triples. -/
noncomputable def guardPoly (T : ℤ) : MvPolynomial (Fin 15) ℤ :=
  ∏ t ∈ falseTriples T, guardFactor t

theorem guardPoly_of_neg {T : ℤ} (hT : T < 0) : guardPoly T = 1 := by
  rw [guardPoly, Finset.prod_eq_one]
  intro t ht
  have h := (Finset.mem_filter.1 ht).1
  simp only [guardBox, Finset.mem_product, Finset.mem_Icc] at h
  omega

/-! ### The rational zero set -/

/-- `(D_abc / B_j) A_j = D_abc · (A_j / B_j)` in `ℚ`. -/
theorem div_den_mul_num (t : ℤ × ℤ × ℤ) (j : Fin 15) :
    ((((tripleDen t / (tripleCode t j).den : ℕ) : ℤ) * (tripleCode t j).num : ℤ) : ℚ) =
      (tripleDen t : ℚ) * tripleCode t j := by
  obtain ⟨k, hk⟩ := den_dvd_tripleDen t j
  rw [hk, Nat.mul_div_cancel_left _ (tripleCode t j).den_pos]
  have := Rat.mul_den_eq_num (tripleCode t j)
  push_cast
  linear_combination (-(k : ℚ)) * this

/-- The value of a factor at a rational point is `∑_j (D_abc (x_j - A_j/B_j))²`. -/
theorem eval_guardFactor (x : Fin 15 → ℚ) (t : ℤ × ℤ × ℤ) :
    eval₂ (Int.castRingHom ℚ) x (guardFactor t) =
      ∑ j, ((tripleDen t : ℚ) * (x j - tripleCode t j)) ^ 2 := by
  simp only [guardFactor, eval₂_sum, eval₂_pow, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eq_intCast, eq_intCast, div_den_mul_num, mul_sub]
  push_cast
  ring

/-- A factor vanishes at a rational point exactly at the triple code. -/
theorem eval_guardFactor_eq_zero_iff (x : Fin 15 → ℚ) (t : ℤ × ℤ × ℤ) :
    eval₂ (Int.castRingHom ℚ) x (guardFactor t) = 0 ↔ x = tripleCode t := by
  have hD : (tripleDen t : ℚ) ≠ 0 := by exact_mod_cast (tripleDen_pos t).ne'
  rw [eval_guardFactor]
  constructor
  · intro h
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun j => ((tripleDen t : ℚ) * (x j - tripleCode t j)) ^ 2)
      fun j _ => sq_nonneg _).1 h j (Finset.mem_univ j)
    rw [sq_eq_zero_iff, mul_eq_zero, sub_eq_zero] at hj
    exact hj.resolve_left hD
  · rintro rfl
    exact Finset.sum_eq_zero fun j _ => by rw [sub_self, mul_zero, sq, mul_zero]

/-- The rational zero set of `G_T` is the set of codes of the false triples in the box. -/
theorem guardPoly_eval_eq_zero_iff (T : ℤ) (x : Fin 15 → ℚ) :
    eval₂ (Int.castRingHom ℚ) x (guardPoly T) = 0 ↔
      ∃ a b c : ℤ, |a| ≤ T ∧ |b| ≤ T ∧ |c| ≤ T ∧ a * b ≠ c ∧ x = tripleCode (a, b, c) := by
  rw [guardPoly, eval₂_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨⟨a, b, c⟩, ht, h⟩
    exact ⟨a, b, c, mem_falseTriples.1 ht |>.1, mem_falseTriples.1 ht |>.2.1,
      mem_falseTriples.1 ht |>.2.2.1, mem_falseTriples.1 ht |>.2.2.2,
      (eval_guardFactor_eq_zero_iff x _).1 h⟩
  · rintro ⟨a, b, c, ha, hb, hc, hab, hx⟩
    exact ⟨(a, b, c), mem_falseTriples.2 ⟨ha, hb, hc, hab⟩,
      (eval_guardFactor_eq_zero_iff x _).2 hx⟩

end ZInQ.Syntax
