/-
Plan steps 3.4–3.5 (effective Dirichlet): for a real character `χ ≠ 1` modulo `q`,
`‖L(1, χ)‖ ≥ log((1 + √5)/2) / (18 q √q) ≥ 1 / (40 q √q)`.
-/
import ZInQKernel.Progressions.Final.RealLimit
import ZInQKernel.Progressions.QuadField
import ZInQKernel.Progressions.RealChar

namespace ZInQ.Progressions

open NumberField

/-- The Euler-factor quotient at `s = 1`: `‖(1 - a/p)(1 - b/p)⁻¹‖ ≤ (p + 1)/(p - 1)` when
`‖a‖, ‖b‖ ≤ 1` and `p ≥ 2`. -/
theorem norm_localFactor_one_le {p : ℕ} (hp : 2 ≤ p) {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖(1 - a * (p : ℂ) ^ (-(1 : ℂ))) * (1 - b * (p : ℂ) ^ (-(1 : ℂ)))⁻¹‖ ≤
      ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  rw [Complex.cpow_neg_one, norm_mul, norm_inv]
  have hap : ‖a * (p : ℂ)⁻¹‖ ≤ 1 / p := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, one_div]
    exact mul_le_of_le_one_left (by positivity) ha
  have hbp : ‖b * (p : ℂ)⁻¹‖ ≤ 1 / p := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, one_div]
    exact mul_le_of_le_one_left (by positivity) hb
  have h1 : ‖1 - a * (p : ℂ)⁻¹‖ ≤ 1 + 1 / p := by
    calc ‖1 - a * (p : ℂ)⁻¹‖ ≤ ‖(1 : ℂ)‖ + ‖a * (p : ℂ)⁻¹‖ := norm_sub_le _ _
      _ ≤ 1 + 1 / p := by rw [norm_one]; linarith
  have hinv : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
  have h2 : 1 - 1 / p ≤ ‖1 - b * (p : ℂ)⁻¹‖ := by
    have := norm_sub_norm_le (1 : ℂ) (b * (p : ℂ)⁻¹)
    rw [norm_one] at this
    linarith
  have h2pos : 0 < 1 - 1 / (p : ℝ) := by linarith
  calc ‖1 - a * (p : ℂ)⁻¹‖ * ‖1 - b * (p : ℂ)⁻¹‖⁻¹ ≤ (1 + 1 / p) * (1 - 1 / (p : ℝ))⁻¹ :=
        mul_le_mul h1 (inv_anti₀ h2pos h2) (inv_nonneg.2 (norm_nonneg _)) (by positivity)
    _ = ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
        have : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp

/-- `∏_{p ∣ 2q} (p + 1)/(p - 1) ≤ 3q`: the factor at `2` is `3`, and `(p + 1)/(p - 1) ≤ p` for
`p ≥ 3`. -/
theorem prod_primeFactors_two_mul_le {q : ℕ} (hq : q ≠ 0) :
    ∏ p ∈ (2 * q).primeFactors, ((p : ℝ) + 1) / ((p : ℝ) - 1) ≤ 3 * q := by
  have h2q : 2 * q ≠ 0 := by omega
  have h2mem : 2 ∈ (2 * q).primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, dvd_mul_right 2 q, h2q⟩
  rw [← Finset.mul_prod_erase _ _ h2mem]
  have hle : ∏ p ∈ (2 * q).primeFactors.erase 2, ((p : ℝ) + 1) / ((p : ℝ) - 1) ≤
      ∏ p ∈ (2 * q).primeFactors.erase 2, (p : ℝ) := by
    refine Finset.prod_le_prod₀ (fun p hp ↦ ?_) fun p hp ↦ ?_
    · have hp2 := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      exact div_nonneg (by linarith) (by linarith)
    · have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have hp3 : 3 ≤ p := by
        have := hpp.two_le
        have := Finset.ne_of_mem_erase hp
        omega
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hprod : 2 * ∏ p ∈ (2 * q).primeFactors.erase 2, (p : ℝ) ≤ 2 * q := by
    rw [← Nat.cast_prod, show (2 : ℝ) * _ = ((2 * ∏ p ∈ (2 * q).primeFactors.erase 2, p : ℕ) : ℝ)
      by push_cast; ring, Finset.mul_prod_erase _ (fun p : ℕ ↦ p) h2mem]
    exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd (2 * q))
  have h0 : 0 ≤ ∏ p ∈ (2 * q).primeFactors.erase 2, ((p : ℝ) + 1) / ((p : ℝ) - 1) := by
    refine Finset.prod_nonneg fun p hp ↦ ?_
    have hp2 := (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    exact div_nonneg (by linarith) (by linarith)
  rw [show (((2 : ℕ) : ℝ) + 1) / (((2 : ℕ) : ℝ) - 1) = 3 by norm_num]
  nlinarith

/-- `log((1 + √5)/2) ≥ 9/20`: with `φ = (1 + √5)/2`, `φ² = φ + 1 ≥ 13/5`, so
`2 log φ = log 2 + log(φ²/2) ≥ log 2 + 1 - 2/φ² ≥ 0.69 + 3/13`. -/
theorem nine_twentieths_le_log_golden : 9 / 20 ≤ Real.log ((1 + √5) / 2) := by
  have h5 : 11 / 5 ≤ √5 := Real.le_sqrt_of_sq_le (by norm_num)
  set φ := (1 + √5) / 2 with hφ
  have hφ0 : 0 < φ := by rw [hφ]; positivity
  have hφ2 : φ ^ 2 = φ + 1 := by
    rw [hφ, div_pow, add_sq, Real.sq_sqrt (by norm_num)]; ring
  have hφ13 : 13 / 5 ≤ φ ^ 2 := by rw [hφ2, hφ]; linarith
  have hlog : Real.log (φ ^ 2) = Real.log 2 + Real.log (φ ^ 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]; ring
  have h1 := Real.one_sub_inv_le_log_of_pos (x := φ ^ 2 / 2) (by positivity)
  have hinv : (φ ^ 2 / 2)⁻¹ ≤ 10 / 13 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have h2 := Real.log_two_gt_d9
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **Real characters** (plan steps 3.4–3.5, sharp form). For a Dirichlet character `χ ≠ 1`
modulo `q` with `χ ^ 2 = 1`, `‖L(1, χ)‖ ≥ log((1 + √5)/2) / (18 q √q)`. -/
theorem log_golden_div_le_norm_LFunction_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 = 1) :
    Real.log ((1 + √5) / 2) / (18 * (q * √q)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  have hq0 : q ≠ 0 := NeZero.ne q
  obtain ⟨d, hsq, hd1, hdvd, -, hleg⟩ :=
    exists_legendre_of_real_char_dvd (Nat.one_le_iff_ne_zero.2 hq0) χ hχ1 hχ2
  have : Fact (¬ IsSquare (d : ℚ)) := ⟨Qsqrt.not_isSquare_of_squarefree hsq hd1⟩
  have hdZ : ¬ IsSquare d := fun h ↦
    (Fact.out : ¬ IsSquare (d : ℚ)) (Rat.isSquare_intCast_iff.2 h)
  have hdq : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → ¬ (p : ℤ) ∣ d := fun p _ hpq hpd ↦
    hpq (dvd_mul_of_dvd_right ((Int.natCast_dvd.1 hpd).trans hdvd) 2)
  have hres := dedekindZeta_residue_eq_LFunction_one_mul_prod (K := Qsqrt d) Qsqrt.finrank
    Qsqrt.sqrtInt_sq hdZ χ hχ1 hdq hleg
  set P := ∏ p ∈ (2 * q).primeFactors,
    (1 - χ p * (p : ℂ) ^ (-(1 : ℂ))) * (1 - localEps (Qsqrt d) p * (p : ℂ) ^ (-(1 : ℂ)))⁻¹
  have hnorm : dedekindZeta_residue (Qsqrt d) = ‖DirichletCharacter.LFunction χ 1‖ * ‖P‖ := by
    rw [← norm_mul, ← hres, Complex.norm_real,
      Real.norm_of_nonneg (dedekindZeta_residue_pos _).le]
  have hP : ‖P‖ ≤ 3 * q := by
    refine (Finset.norm_prod_le _ _).trans <| le_trans (Finset.prod_le_prod₀
      (fun p _ ↦ norm_nonneg _) fun p hp ↦ ?_) (prod_primeFactors_two_mul_le hq0)
    have hp := Nat.prime_of_mem_primeFactors hp
    exact norm_localFactor_one_le hp.two_le (DirichletCharacter.norm_le_one χ _)
      (IdealCount.norm_localEps_le_one Qsqrt.finrank hp)
  have hlow := dedekindZeta_residue_ge (d := d)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hq0
  have hdle : |(d : ℝ)| ≤ q := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast Nat.le_of_dvd (by omega) hdvd
  have hd0 : 0 < |(d : ℝ)| := abs_pos.2 (by exact_mod_cast (Qsqrt.ne_zero (d := d)))
  have hsd : 0 < √|(d : ℝ)| := Real.sqrt_pos.2 hd0
  have hsq' : √|(d : ℝ)| ≤ √q := Real.sqrt_le_sqrt hdle
  have hlog := log_golden_pos
  have hsqq : 0 < √(q : ℝ) := Real.sqrt_pos.2 (by linarith)
  -- `log φ / (6 √q) ≤ res = ‖L‖ ‖P‖ ≤ ‖L‖ · 3q`
  have h1 : Real.log ((1 + √5) / 2) / (6 * √q) ≤ ‖DirichletCharacter.LFunction χ 1‖ * (3 * q) :=
    calc Real.log ((1 + √5) / 2) / (6 * √q) ≤ Real.log ((1 + √5) / 2) / (6 * √|(d : ℝ)|) := by
          gcongr
      _ ≤ _ := hlow
      _ = _ := hnorm
      _ ≤ _ := by gcongr
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h1
  nlinarith

/-- **Real characters** (plan steps 3.4–3.5). For a Dirichlet character `χ ≠ 1` modulo `q` with
`χ ^ 2 = 1`, `‖L(1, χ)‖ ≥ 1 / (40 q^(3/2))`, with `q^(3/2)` written `q √q`. -/
theorem norm_LFunction_one_ge_of_sq_eq_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ2 : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    1 / (40 * (q * √q)) ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  refine le_trans ?_ (log_golden_div_le_norm_LFunction_one hχ1 hχ2)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have : 0 < (q : ℝ) * √q := mul_pos (by linarith) (Real.sqrt_pos.2 (by linarith))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [nine_twentieths_le_log_golden]

end ZInQ.Progressions
