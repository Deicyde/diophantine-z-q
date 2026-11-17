import Mathlib

/-!
# pb-sanity: the truncated logarithm identity in `ℚ[B][A]` (towards `LogAdditive`)

`F_M = L_M(A + B + AB) - L_M(A) - L_M(B)`, `L_M(Z) = Σ_{1 ≤ j ≤ M} (-1)^{j+1} Z^j / j`.
Claim 1: every monomial `A^i B^s` of `F_M` with `i + s ≤ M` has coefficient 0.
-/

noncomputable section

open Polynomial

namespace PBLogPoly

abbrev R := Polynomial ℚ
abbrev S := Polynomial R

/-- `κ j = (-1)^{j+1}/j`. -/
def κ (j : ℕ) : ℚ := (-1) ^ (j + 1) / j

/-- `L_M(Z) = Σ_{1 ≤ j ≤ M} κ_j Z^j`. -/
def LM (M : ℕ) (Z : S) : S := ∑ j ∈ Finset.Ico 1 (M + 1), C (C (κ j)) * Z ^ j

/-- `c = A(1 + B) + B`, i.e. `(1 + A)(1 + B) - 1`. -/
def cA : S := X * C (1 + X) + C X

/-- `F_M = L_M(c) - L_M(A) - L_M(B)`. -/
def FM (M : ℕ) : S := LM M cA - LM M X - LM M (C X)

theorem derivative_LM (M : ℕ) (Z : S) :
    derivative (LM M Z) = (∑ k ∈ Finset.range M, (-Z) ^ k) * derivative Z := by
  rw [LM, derivative_sum, Finset.sum_Ico_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [derivative_C_mul, derivative_pow]
  have hk : ((1 + k : ℕ) : S) * C (C (κ (1 + k))) = (-1) ^ k := by
    have : ((1 + k : ℕ) : ℚ) * κ (1 + k) = (-1) ^ k := by
      rw [κ]
      have h0 : ((1 + k : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp
      ring
    have := congrArg (fun q : ℚ => (C (C q) : S)) this
    simpa [map_mul, map_pow, map_neg, map_one] using this
  rw [Nat.add_sub_cancel_left]
  calc C (C (κ (1 + k))) * (C ((1 + k : ℕ) : R) * Z ^ k * derivative Z)
      = (((1 + k : ℕ) : S) * C (C (κ (1 + k)))) * Z ^ k * derivative Z := by
        rw [show (C ((1 + k : ℕ) : R) : S) = ((1 + k : ℕ) : S) from map_natCast C _]
        ring
    _ = _ := by rw [hk]; ring

theorem geom_neg (M : ℕ) (z : S) :
    (1 + z) * ∑ k ∈ Finset.range M, (-z) ^ k = 1 - (-z) ^ M := by
  have := geom_sum_mul_neg (-z) M
  rw [mul_comm, ← this]
  ring

theorem key_identity (M : ℕ) :
    (1 + X) * derivative (FM M) = (-X) ^ M - (-cA) ^ M := by
  have hc : derivative cA = C (1 + X) := by
    simp [cA, derivative_mul]
  have h1 : (1 + X : S) * C (1 + X) = 1 + cA := by
    simp only [cA, map_add, map_one]
    ring
  rw [FM, derivative_sub, derivative_sub, derivative_LM, derivative_LM, derivative_LM, hc,
    derivative_X, derivative_C, mul_zero, sub_zero, mul_one, mul_sub]
  rw [show (1 + X : S) * ((∑ k ∈ Finset.range M, (-cA) ^ k) * C (1 + X)) =
    (1 + cA) * ∑ k ∈ Finset.range M, (-cA) ^ k by rw [← h1]; ring]
  rw [geom_neg, geom_neg]
  ring

/-- The coefficients of `c^k` in `A` are divisible by suitable powers of `B`. -/
theorem dvd_coeff_cA_pow (k : ℕ) : ∀ i, (X : R) ^ (k - i) ∣ (cA ^ k).coeff i := by
  induction k with
  | zero =>
    intro i
    rw [Nat.zero_sub, pow_zero]
    exact one_dvd _
  | succ k ih =>
    intro i
    rw [pow_succ, cA, mul_add, ← mul_assoc, coeff_add, coeff_mul_C, coeff_mul_C]
    refine dvd_add ?_ ?_
    · rcases i with _ | i
      · rw [coeff_mul_X_zero, zero_mul]
        exact dvd_zero _
      · rw [coeff_mul_X, show k + 1 - (i + 1) = k - i by omega]
        exact dvd_mul_of_dvd_left (ih i) _
    · have := ih i
      calc (X : R) ^ (k + 1 - i) ∣ (X : R) ^ (k - i) * X := by
            rw [← pow_succ]; exact pow_dvd_pow X (by omega)
        _ ∣ (cA ^ k).coeff i * X := mul_dvd_mul_right this _

theorem eval_zero_LM (M : ℕ) (Z : S) :
    eval 0 (LM M Z) = ∑ j ∈ Finset.Ico 1 (M + 1), C (κ j) * (eval 0 Z) ^ j := by
  simp [LM, eval_finsetSum]

theorem coeff_zero_FM (M : ℕ) : (FM M).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, FM, eval_sub, eval_sub, eval_zero_LM, eval_zero_LM, eval_zero_LM]
  have h1 : eval 0 cA = X := by simp [cA]
  rw [h1, eval_X, eval_C, sub_sub_cancel_left, neg_eq_zero]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [zero_pow (by omega), mul_zero]

theorem dvd_coeff_rhs (M i : ℕ) : (X : R) ^ (M - i) ∣ ((-X) ^ M - (-cA) ^ M : S).coeff i := by
  rcases Nat.lt_or_ge i M with h | h
  · rw [coeff_sub, _root_.neg_pow (X : S), _root_.neg_pow (cA : S),
      show ((-1 : S) ^ M) = C ((-1) ^ M) by simp, coeff_C_mul_X_pow, coeff_C_mul]
    split_ifs with h'
    · omega
    · rw [zero_sub]
      exact (dvd_neg).mpr (dvd_mul_of_dvd_right (dvd_coeff_cA_pow M i) _)
  · rw [show M - i = 0 by omega, pow_zero]
    exact one_dvd _

/-- **Claim 1 (divisibility form).** `B^{M+1-i}` divides the coefficient of `A^i` in `F_M`. -/
theorem dvd_coeff_FM (M : ℕ) : ∀ i, (X : R) ^ (M + 1 - i) ∣ (FM M).coeff i := by
  intro i
  induction i with
  | zero => rw [coeff_zero_FM]; exact dvd_zero _
  | succ i ih =>
    have hid := congrArg (fun P : S => P.coeff i) (key_identity M)
    rw [add_mul, one_mul, coeff_add, coeff_derivative] at hid
    have hX : (X : R) ^ (M - i) ∣ (X * derivative (FM M)).coeff i := by
      rcases i with _ | i
      · rw [coeff_X_mul_zero]; exact dvd_zero _
      · rw [coeff_X_mul, coeff_derivative]
        refine dvd_mul_of_dvd_left ((pow_dvd_pow X (by omega)).trans ih) _
    have h2 : (X : R) ^ (M - i) ∣ (FM M).coeff (i + 1) * ((i : R) + 1) := by
      have : (FM M).coeff (i + 1) * ((i : R) + 1) =
          ((-X) ^ M - (-cA) ^ M : S).coeff i - (X * derivative (FM M)).coeff i := by
        rw [← hid]; ring
      rw [this]
      exact dvd_sub (dvd_coeff_rhs M i) hX
    have hu : IsUnit ((i : R) + 1) := by
      have : ((i : R) + 1) = C ((i : ℚ) + 1) := by simp
      rw [this]
      exact (Polynomial.isUnit_C).mpr (IsUnit.mk0 _ (by positivity))
    rw [show M + 1 - (i + 1) = M - i by omega]
    exact (hu.dvd_mul_right).mp h2

/-- **Claim 1.** The coefficient of `A^i B^s` in `F_M` vanishes for `i + s ≤ M`. -/
theorem coeff_FM_eq_zero (M i s : ℕ) (h : i + s ≤ M) : ((FM M).coeff i).coeff s = 0 := by
  obtain ⟨g, hg⟩ := dvd_coeff_FM M i
  rw [hg, coeff_X_pow_mul']
  split_ifs with h'
  · omega
  · rfl

/-! ### Divided-power integrality -/

/-- All coefficients of `F` in the basis `A^i B^s / (i! s!)` are integers. -/
def IsDPInt (F : S) : Prop :=
  ∀ i s, ∃ z : ℤ, (F.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ) = z

theorem isDPInt_add {F G : S} (hF : IsDPInt F) (hG : IsDPInt G) : IsDPInt (F + G) := by
  intro i s
  obtain ⟨a, ha⟩ := hF i s
  obtain ⟨b, hb⟩ := hG i s
  exact ⟨a + b, by rw [coeff_add, coeff_add, add_mul, add_mul, ha, hb]; push_cast; ring⟩

theorem isDPInt_neg {F : S} (hF : IsDPInt F) : IsDPInt (-F) := by
  intro i s
  obtain ⟨a, ha⟩ := hF i s
  exact ⟨-a, by rw [coeff_neg, coeff_neg, neg_mul, neg_mul, ha]; push_cast; ring⟩

theorem isDPInt_sum {ι : Type*} (t : Finset ι) (F : ι → S) (h : ∀ k ∈ t, IsDPInt (F k)) :
    IsDPInt (∑ k ∈ t, F k) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro i s; exact ⟨0, by simp⟩
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact isDPInt_add (h a (Finset.mem_insert_self a t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem isDPInt_mul {F G : S} (hF : IsDPInt F) (hG : IsDPInt G) : IsDPInt (F * G) := by
  classical
  choose a ha using hF
  choose b hb using hG
  intro i s
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal i, ∑ y ∈ Finset.HasAntidiagonal.antidiagonal s,
    ((i.choose x.1 * s.choose y.1 : ℕ) : ℤ) * a x.1 y.1 * b x.2 y.2, ?_⟩
  rw [coeff_mul, finsetSum_coeff, Finset.sum_mul, Finset.sum_mul]
  push_cast
  apply Finset.sum_congr rfl
  intro x hx
  rw [coeff_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx hy
  have hxi : (i.factorial : ℚ) = (i.choose x.1 : ℚ) * x.1.factorial * x.2.factorial := by
    rw [← hx, Nat.choose_symm_add]
    have := Nat.add_choose_mul_factorial_mul_factorial x.1 x.2
    exact_mod_cast this.symm
  have hys : (s.factorial : ℚ) = (s.choose y.1 : ℚ) * y.1.factorial * y.2.factorial := by
    rw [← hy, Nat.choose_symm_add]
    have := Nat.add_choose_mul_factorial_mul_factorial y.1 y.2
    exact_mod_cast this.symm
  rw [← ha x.1 y.1, ← hb x.2 y.2, hxi, hys]
  ring

theorem isDPInt_C_C_int (z : ℤ) : IsDPInt (C (C (z : ℚ))) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [coeff_C]
    split_ifs with hs
    · subst hs; exact ⟨z, by simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem isDPInt_one : IsDPInt 1 := by
  have := isDPInt_C_C_int 1
  simpa using this

/-- `γ_r(A) = A^r / r!`. -/
theorem isDPInt_dpowA (r : ℕ) : IsDPInt (C (C ((r.factorial : ℚ)⁻¹)) * X ^ r) := by
  intro i s
  rw [coeff_C_mul_X_pow]
  split_ifs with hi
  · subst hi
    rw [coeff_C]
    split_ifs with hs
    · subst hs
      exact ⟨1, by
        rw [Nat.factorial_zero, Nat.cast_one, mul_one,
          inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i)]; simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

/-- `γ_k(B) = B^k / k!`. -/
theorem isDPInt_dpowB (k : ℕ) : IsDPInt (C (C ((k.factorial : ℚ)⁻¹) * X ^ k)) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [coeff_C_mul_X_pow]
    split_ifs with hs
    · subst hs
      exact ⟨1, by
        rw [Nat.factorial_zero, Nat.cast_one, mul_one,
          inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero s)]; simp⟩
    · exact ⟨0, by simp⟩
  · exact ⟨0, by simp⟩

theorem isDPInt_C_one_add_X_pow (r : ℕ) : IsDPInt (C ((1 + X : R) ^ r)) := by
  intro i s
  rw [coeff_C]
  split_ifs with hi
  · subst hi
    rw [add_comm, coeff_X_add_one_pow]
    exact ⟨(r.choose s * s.factorial : ℕ), by push_cast; ring⟩
  · exact ⟨0, by simp⟩

/-- Divided binomial theorem: `(u + v)^j / j! = Σ_r u^r/r! · v^{j-r}/(j-r)!`. -/
theorem dpow_add_S (j : ℕ) (u v : S) :
    C (C ((j.factorial : ℚ)⁻¹)) * (u + v) ^ j =
      ∑ r ∈ Finset.range (j + 1), (C (C ((r.factorial : ℚ)⁻¹)) * u ^ r) *
        (C (C (((j - r).factorial : ℚ)⁻¹)) * v ^ (j - r)) := by
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hc : ((j.choose r : ℕ) : S) * C (C ((j.factorial : ℚ)⁻¹)) =
      C (C ((r.factorial : ℚ)⁻¹)) * C (C (((j - r).factorial : ℚ)⁻¹)) := by
    rw [← map_natCast C, ← map_natCast C, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    have h := Nat.choose_mul_factorial_mul_factorial (show r ≤ j by omega)
    have h2 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
    have h3 : ((j - r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j - r)
    have h4 : ((j.choose r : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (show r ≤ j by omega)).ne'
    rw [← h]
    push_cast
    field_simp
  calc C (C ((j.factorial : ℚ)⁻¹)) * (u ^ r * v ^ (j - r) * (j.choose r : S))
      = (((j.choose r : ℕ) : S) * C (C ((j.factorial : ℚ)⁻¹))) * (u ^ r * v ^ (j - r)) := by ring
    _ = _ := by rw [hc]; ring

/-- `γ_j(c) = c^j / j!` is divided-power integral. -/
theorem isDPInt_dpow_cA (j : ℕ) : IsDPInt (C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j) := by
  rw [cA, dpow_add_S]
  apply isDPInt_sum
  intro r _
  apply isDPInt_mul
  · rw [mul_pow, ← map_pow, ← mul_assoc]
    exact isDPInt_mul (isDPInt_dpowA r) (isDPInt_C_one_add_X_pow r)
  · rw [← map_pow, ← map_mul]
    exact isDPInt_dpowB (j - r)

/-! ### Support of `c^k` -/

theorem cA_pow_succ (k : ℕ) : cA ^ (k + 1) = cA ^ k * X * C (1 + X) + cA ^ k * C X := by
  rw [pow_succ]; unfold cA; ring

theorem coeff_cA_pow_eq_zero (k : ℕ) : ∀ i s, (k < i ∨ k < s) → ((cA ^ k).coeff i).coeff s = 0 := by
  induction k with
  | zero =>
    intro i s h
    rw [pow_zero, coeff_one]
    split_ifs with hi
    · subst hi
      rw [coeff_one]
      split_ifs with hs
      · omega
      · rfl
    · rfl
  | succ k ih =>
    intro i s h
    rw [cA_pow_succ, coeff_add, coeff_mul_C, coeff_mul_C, coeff_add]
    rcases i with _ | i
    · rw [coeff_mul_X_zero, zero_mul, coeff_zero, zero_add]
      rcases s with _ | s
      · rw [coeff_mul_X_zero]
      · rw [coeff_mul_X]
        exact ih 0 s (by omega)
    · rw [coeff_mul_X, mul_add, mul_one, coeff_add]
      have h1 : ((cA ^ k).coeff i).coeff s = 0 := ih i s (by omega)
      have h2 : ((cA ^ k).coeff i * X).coeff s = 0 := by
        rcases s with _ | s
        · rw [coeff_mul_X_zero]
        · rw [coeff_mul_X]; exact ih i s (by omega)
      have h3 : ((cA ^ k).coeff (i + 1) * X).coeff s = 0 := by
        rcases s with _ | s
        · rw [coeff_mul_X_zero]
        · rw [coeff_mul_X]; exact ih (i + 1) s (by omega)
      rw [h1, h2, h3]
      ring

/-! ### High coefficients of `F_M` are divisible by `N` when `M ≥ 2N + 1` -/

theorem κ_eq (j : ℕ) (hj : 1 ≤ j) :
    κ j = (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) * ((j.factorial : ℚ)⁻¹) := by
  have h := Nat.mul_factorial_pred (show j ≠ 0 by omega)
  have h1 : ((j - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (j : ℚ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [κ, ← h]
  push_cast
  field_simp

theorem FM_eq_sum (M : ℕ) : FM M = ∑ j ∈ Finset.Ico 1 (M + 1),
    C (C ((-1) ^ (j + 1) * ((j - 1).factorial : ℚ))) *
      (C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j - C (C ((j.factorial : ℚ)⁻¹)) * X ^ j -
        C (C ((j.factorial : ℚ)⁻¹) * X ^ j)) := by
  rw [FM, LM, LM, LM, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [κ_eq j hj.1]
  simp only [map_mul, map_pow]
  ring

theorem exists_sum_eq_mul (N : ℕ) (t : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ j ∈ t, ∃ z : ℤ, f j = N * z) : ∃ z : ℤ, ∑ j ∈ t, f j = N * z := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a t ha ih =>
    obtain ⟨z1, hz1⟩ := h a (Finset.mem_insert_self a t)
    obtain ⟨z2, hz2⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    exact ⟨z1 + z2, by rw [Finset.sum_insert ha, hz1, hz2]; push_cast; ring⟩

/-- **Claim 2.** If `M ≥ 2N + 1`, every coefficient of `F_M` in the basis `A^i B^s/(i! s!)` is
divisible by `N`. -/
theorem FM_coeff_dvd (N M : ℕ) (hN : 0 < N) (hNM : 2 * N + 1 ≤ M) (i s : ℕ) :
    ∃ z : ℤ, ((FM M).coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ) = N * z := by
  by_cases hlow : i + s ≤ M
  · exact ⟨0, by rw [coeff_FM_eq_zero M i s hlow]; simp⟩
  push Not at hlow
  rw [FM_eq_sum, finsetSum_coeff, finsetSum_coeff, Finset.sum_mul, Finset.sum_mul]
  apply exists_sum_eq_mul
  intro j hj
  rw [Finset.mem_Ico] at hj
  rw [coeff_C_mul, coeff_C_mul]
  set G : S := C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j - C (C ((j.factorial : ℚ)⁻¹)) * X ^ j -
    C (C ((j.factorial : ℚ)⁻¹) * X ^ j) with hG
  have hGint : IsDPInt G := by
    rw [hG, sub_eq_add_neg, sub_eq_add_neg]
    refine isDPInt_add (isDPInt_add (isDPInt_dpow_cA j) (isDPInt_neg (isDPInt_dpowA j)))
      (isDPInt_neg (isDPInt_dpowB j))
  obtain ⟨w, hw⟩ := hGint i s
  by_cases hjN : N + 1 ≤ j
  · obtain ⟨e, he⟩ := Nat.dvd_factorial hN (show N ≤ j - 1 by omega)
    refine ⟨(-1) ^ (j + 1) * e * w, ?_⟩
    rw [show (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) * (G.coeff i).coeff s * (i.factorial : ℚ) *
        (s.factorial : ℚ) = (-1) ^ (j + 1) * ((j - 1).factorial : ℚ) *
          ((G.coeff i).coeff s * (i.factorial : ℚ) * (s.factorial : ℚ)) by ring, hw, he]
    push_cast
    ring
  · have h1 : ((C (C ((j.factorial : ℚ)⁻¹)) * cA ^ j : S).coeff i).coeff s = 0 := by
      rw [coeff_C_mul, coeff_C_mul, coeff_cA_pow_eq_zero j i s (by omega), mul_zero]
    have h2 : ((C (C ((j.factorial : ℚ)⁻¹)) * X ^ j : S).coeff i).coeff s = 0 := by
      rw [coeff_C_mul_X_pow]
      split_ifs with hij
      · rw [coeff_C]
        split_ifs with hs0
        · omega
        · rfl
      · rfl
    have h3 : ((C (C ((j.factorial : ℚ)⁻¹) * X ^ j) : S).coeff i).coeff s = 0 := by
      rw [coeff_C]
      split_ifs with hi0
      · rw [coeff_C_mul_X_pow]
        split_ifs with hsj
        · omega
        · rfl
      · rfl
    have hG0 : (G.coeff i).coeff s = 0 := by
      rw [hG, coeff_sub, coeff_sub, coeff_sub, coeff_sub, h1, h2, h3, sub_zero, sub_zero]
    exact ⟨0, by rw [hG0]; simp⟩

end PBLogPoly
