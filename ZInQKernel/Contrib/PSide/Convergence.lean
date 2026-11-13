import ZInQKernel.Contrib.PSide.Hasse
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# P4 (second half): `L(C_d, s)` converges absolutely on `Re s > 3/2`

From Hasse's bound `c_p² ≤ 4p` (`Hasse.lean`) and the recursion
`c_{p^{k+2}} = c_p c_{p^{k+1}} − p c_{p^k}` (`Coeff.lean`):

* `recurrence_bound`: a real sequence with `u₀ = 1`, `u₁ = a`, `u_{k+2} = a u_{k+1} − r² u_k` and
  `a² ≤ 4r²` satisfies `|u_k| ≤ (k + 1) r^k` (write `u_k = Σ_{i ≤ k} α^i β^{k−i}` with the complex
  roots `α, β = (a ± i√(4r² − a²))/2` of modulus `r`);
* `cdCoeff_prime_pow_sq_le`: `c_{p^k}² ≤ (k + 1)² p^k` for every prime `p` (also at `p ∣ 2d`);
* `cdCoeff_sq_le`: `c_n² ≤ σ₀(n)² n` for every `n` (multiplicativity);
* `LSeriesSummable_cdCoeff`: the Dirichlet series `Σ c_n n^{−s}` converges absolutely for
  `Re s > 3/2` (comparison with `Σ σ₀(n) n^{−(s − 1/2)} = ζ(s − 1/2)²`, Mathlib's
  `LSeriesSummable.convolution`);
* on Mathlib's `L(C_d, s)` (odd squarefree `d`): `LSeriesSummable_cd`,
  `abscissaOfAbsConv_cd_le` (`≤ 3/2`) and `differentiableOn_LSeries_cd` (holomorphic on
  `Re s > 3/2`). So the condition `F s = E.LSeries s` for `3/2 < Re s` in `IsLContinuation`
  (`Hypotheses/CR3Literature.lean`) compares `F` with an absolutely convergent series.
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature WeierstrassCurve ArithmeticFunction
open scoped LSeries.notation

/-- **Second-order recurrences with complex roots of modulus `r` grow at most linearly**. -/
theorem recurrence_bound (a r : ℝ) (hr : 0 ≤ r) (ha : a ^ 2 ≤ 4 * r ^ 2) (u : ℕ → ℝ)
    (h0 : u 0 = 1) (h1 : u 1 = a) (hrec : ∀ k, u (k + 2) = a * u (k + 1) - r ^ 2 * u k) :
    ∀ k, |u k| ≤ (k + 1) * r ^ k := by
  set dl := Real.sqrt (4 * r ^ 2 - a ^ 2)
  have hdl : dl ^ 2 = 4 * r ^ 2 - a ^ 2 := Real.sq_sqrt (by linarith)
  set α : ℂ := ⟨a / 2, dl / 2⟩
  set β : ℂ := ⟨a / 2, -dl / 2⟩
  have hsum : α + β = (a : ℂ) := by apply Complex.ext <;> simp [α, β] <;> ring
  have hprod : α * β = (r : ℂ) ^ 2 := by
    apply Complex.ext
    · simp only [α, β, Complex.mul_re, sq, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re]
      nlinarith
    · simp only [α, β, Complex.mul_im, sq, Complex.ofReal_re, Complex.ofReal_im]
      ring
  have hnα : ‖α‖ = r := by
    rw [Complex.norm_def, Complex.normSq_mk, ← Real.sqrt_sq hr]
    congr 1; nlinarith
  have hnβ : ‖β‖ = r := by
    rw [Complex.norm_def, Complex.normSq_mk, ← Real.sqrt_sq hr]
    congr 1; nlinarith
  let s : ℕ → ℂ := fun k => ∑ i ∈ Finset.range (k + 1), α ^ i * β ^ (k - i)
  have hs0 : s 0 = 1 := by simp [s]
  have hs_succ : ∀ k, s (k + 1) = α ^ (k + 1) + β * s k := by
    intro k
    simp only [s]
    rw [Finset.sum_range_succ, Finset.mul_sum, add_comm, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
    ring
  have hs_eq : ∀ k, (u k : ℂ) = s k ∧ (u (k + 1) : ℂ) = s (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [h0, hs0]; simp, ?_⟩
      rw [hs_succ, hs0, h1, ← hsum]; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec]
      push_cast
      rw [ih.1, ih.2]
      have e2 := hs_succ (k + 1)
      have e1 := hs_succ k
      linear_combination -e2 + α * e1 - s (k + 1) * hsum + s k * hprod
  have hs_bound : ∀ k, ‖s k‖ ≤ (k + 1) * r ^ k := by
    intro k
    induction k with
    | zero => simp [hs0]
    | succ k ih =>
      rw [hs_succ]
      calc ‖α ^ (k + 1) + β * s k‖ ≤ ‖α‖ ^ (k + 1) + ‖β‖ * ‖s k‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_pow, norm_mul]
        _ ≤ r ^ (k + 1) + r * ((k + 1) * r ^ k) := by
            rw [hnα, hnβ]; gcongr
        _ = ((k + 1 : ℕ) + 1) * r ^ (k + 1) := by push_cast; ring
  intro k
  have := hs_bound k
  rwa [← (hs_eq k).1, Complex.norm_real, Real.norm_eq_abs] at this

/-- **The prime-power bound** `c_{p^k}² ≤ (k + 1)² p^k`, for every prime `p` and every `d`. -/
theorem cdCoeff_prime_pow_sq_le (d : ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cdCoeff d (p ^ k) ^ 2 ≤ ((k : ℤ) + 1) ^ 2 * (p : ℤ) ^ k := by
  by_cases h : p ∣ 2 * d
  · rcases eq_or_ne k 0 with rfl | hk
    · simp [cdCoeff_one]
    · rw [cdCoeff_prime_pow_of_dvd d hp h hk]; positivity
  · have hr : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
    have hr2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
    have key := recurrence_bound (cdCoeff d p : ℝ) (Real.sqrt p) hr
      (by rw [hr2]; exact_mod_cast cdCoeff_prime_sq_le d hp)
      (fun k => (cdCoeff d (p ^ k) : ℝ)) (by simp [cdCoeff_one]) (by simp)
      (fun k => by rw [hr2]; exact_mod_cast cdCoeff_prime_pow_succ_succ d hp h k) k
    have hsq : ((cdCoeff d (p ^ k) : ℝ)) ^ 2 ≤ ((k + 1) * Real.sqrt p ^ k) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) key 2
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, hr2] at hsq
    exact_mod_cast hsq

/-- **The global bound** `c_n² ≤ σ₀(n)² n`, i.e. `|c_n| ≤ σ₀(n) √n`, for every `n` and `d`. -/
theorem cdCoeff_sq_le (d n : ℕ) : cdCoeff d n ^ 2 ≤ ((sigma 0 n : ℕ) : ℤ) ^ 2 * n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ =>
    rw [sigma_zero_apply_prime_pow hp]
    push_cast
    exact cdCoeff_prime_pow_sq_le d hp k
  | zero => simp [cdCoeff_zero]
  | one => simp [cdCoeff_one]
  | coprime m n _ _ hmn hm hn =>
    rw [cdCoeff_mul d hmn, isMultiplicative_sigma.map_mul_of_coprime hmn]
    push_cast
    calc (cdCoeff d m * cdCoeff d n) ^ 2 = cdCoeff d m ^ 2 * cdCoeff d n ^ 2 := by ring
      _ ≤ (((sigma 0 m : ℕ) : ℤ) ^ 2 * m) * (((sigma 0 n : ℕ) : ℤ) ^ 2 * n) :=
          mul_le_mul hm hn (sq_nonneg _) (by positivity)
      _ = _ := by ring

/-- `σ₀` as the Dirichlet convolution `1 ⍟ 1`. -/
theorem convolution_one_one (n : ℕ) :
    (((1 : ℕ → ℂ) ⍟ (1 : ℕ → ℂ)) n) = ((sigma 0 n : ℕ) : ℂ) := by
  simp only [LSeries.convolution_def]
  rw [sigma_zero_apply, ← Nat.map_div_right_divisors, Finset.sum_map]
  simp

/-- **Absolute convergence of `Σ c_n n^{−s}` on `Re s > 3/2`**, for every `d`. -/
theorem LSeriesSummable_cdCoeff (d : ℕ) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n => (cdCoeff d n : ℂ)) s := by
  set s' : ℂ := s - 1 / 2
  have hs' : 1 < s'.re := by
    simp only [s', Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]; linarith
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s' := LSeriesSummable_one_iff.mpr hs'
  have hg : LSeriesSummable ((1 : ℕ → ℂ) ⍟ (1 : ℕ → ℂ)) s' := h1.convolution h1
  refine Summable.of_norm_bounded hg.norm fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn,
    convolution_one_one, Complex.norm_natCast]
  -- `‖c_n‖ ≤ σ₀(n) √n`
  have hb : ‖(cdCoeff d n : ℂ)‖ ≤ (sigma 0 n : ℝ) * Real.sqrt n := by
    rw [Complex.norm_intCast]
    have h := cdCoeff_sq_le d n
    have h' : ((cdCoeff d n : ℝ)) ^ 2 ≤ ((sigma 0 n : ℝ) * Real.sqrt n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn'.le]; exact_mod_cast h
    exact abs_le_of_sq_le_sq' h' (by positivity) |>.2 |> fun h2 =>
      abs_le.mpr ⟨(abs_le_of_sq_le_sq' h' (by positivity)).1, h2⟩
  have hre : s'.re = s.re - 1 / 2 := by
    simp only [s', Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ s'.re * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn', hre]; ring_nf
  rw [hsplit, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖(cdCoeff d n : ℂ)‖ * (n : ℝ) ^ s'.re ≤ ((sigma 0 n : ℝ) * Real.sqrt n) * (n : ℝ) ^ s'.re :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (sigma 0 n : ℝ) * ((n : ℝ) ^ s'.re * Real.sqrt n) := by ring

/-- **Mathlib's `L(C_d, s)` converges absolutely on `Re s > 3/2`** (odd squarefree `d`). -/
theorem LSeriesSummable_cd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    LSeriesSummable ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction) s := by
  have : ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction : ℕ → ℂ) = fun n => (cdCoeff d n : ℂ) := by
    funext n; simp [LFunction_cd_eq_cdCoeff hd hsq]
  rw [this]; exact LSeriesSummable_cdCoeff d hs

/-- The abscissa of absolute convergence of Mathlib's `L(C_d, s)` is at most `3/2`. -/
theorem abscissaOfAbsConv_cd_le {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    LSeries.abscissaOfAbsConv ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction) ≤ (3 / 2 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_cd hd hsq (by simpa using hy)

/-- **Mathlib's `L(C_d, s)` is holomorphic on `Re s > 3/2`** (odd squarefree `d`). -/
theorem differentiableOn_LSeries_cd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    DifferentiableOn ℂ (shortCurve (-(d : ℚ) ^ 2)).LSeries {s : ℂ | 3 / 2 < s.re} := by
  refine (LSeries_differentiableOn _).mono fun s hs => ?_
  simp only [Set.mem_ofPred_eq] at hs ⊢
  calc LSeries.abscissaOfAbsConv ((↑) ∘ (shortCurve (-(d : ℚ) ^ 2)).LFunction) ≤ (3 / 2 : ℝ) :=
        abscissaOfAbsConv_cd_le hd hsq
    _ < s.re := by exact_mod_cast hs

end ZInQ.Contrib.PSide
