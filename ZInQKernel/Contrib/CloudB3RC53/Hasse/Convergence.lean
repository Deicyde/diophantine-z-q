import ZInQKernel.Contrib.CloudB3RC53.Hasse.LocalBound
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Dictionary
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Newform
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# `HasseConvergence` from Hasse's bound

`HasseConvergence` (`RC/PrintsAnalytic`: `∑ a_n n^{-s}` converges absolutely for `Re s > 3/2`, for
every elliptic curve `E/ℚ`) follows from Hasse's bound over finite fields:

* `HasseBound` (statement; PROVED in `WeilIsogeny/HasseProof.lean`; not a print; reference:
  Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Theorem V.1.1): for an elliptic curve `E`
  over a finite field with `q` elements, `| |E(𝔽_q)| − q − 1 | ≤ 2√q`.
* `exists_localPolynomial_roots`: at every prime `p`, Mathlib's local polynomial of `E` is
  `(1 − αT)(1 − βT)` with `|α|, |β| ≤ √p` (good reduction: `HasseBound` for the reduction;
  multiplicative or additive reduction: `1 ∓ T` or `1`).
* `norm_lcoeff_prime_pow_le`: `|a_{p^k}| ≤ (k + 1) p^{k/2}` (`norm_coeff_invOfUnit_le`).
* `norm_lcoeff_le`: `|a_n| ≤ d(n) √n` (multiplicativity of `n ↦ a_n` and of `d = σ₀`).
* `hasseConvergence_of_hasseBound`: `∑ d(n) n^{-t}` is the `L`-series of `ζ ∗ ζ`, summable for
  `Re t > 1`; with `t = s − 1/2` it dominates `∑ |a_n| n^{-Re s}`.

Classification: `hasseConvergence_of_hasseBound` PROVED. `HasseBound`: statement; PROVED
(`WeilIsogeny/HasseProof.lean`, `hasseBoundProved_proof`); not a print — the manuscript uses
Hasse's bound uncited (tex 1590, 6323); Silverman V.1.1 given as a reference only. Hence
`HasseConvergence` holds outright (`Hasse/Final.lean`).
-/

noncomputable section

open Polynomial WeierstrassCurve IsDedekindDomain Rat.HeightOneSpectrum ArithmeticFunction

namespace ZInQ.Contrib.CloudB3RC53.Hasse

/-- **Node `HasseBound`** (statement; PROVED (`WeilIsogeny/HasseProof.lean`); not a print — the
manuscript uses Hasse's bound uncited (tex 1590, 6323); Silverman V.1.1 given as a reference only:
J. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Theorem V.1.1): for an elliptic
curve `E` over a finite field `𝔽_q`, `| |E(𝔽_q)| − q − 1 | ≤ 2√q`. Here `|E(𝔽_q)|` counts the point
at infinity (`W.toAffine.Point` is the affine points together with `O`). -/
def HasseBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (W : WeierstrassCurve F) [W.IsElliptic],
    |(Nat.card W.toAffine.Point : ℝ) - Fintype.card F - 1| ≤ 2 * √(Fintype.card F : ℝ)

/-- **Every local polynomial of `E/ℚ` is `(1 − αT)(1 − βT)` with `|α|, |β| ≤ √p`**, given Hasse's
bound. PROVED from `HasseBound`. -/
theorem exists_localPolynomial_roots (hB : HasseBound) (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ (a b : ℤ) (α β : ℂ), (E.baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 - C a * X + C b * X ^ 2 ∧ α + β = a ∧ α * β = b ∧
      ‖α‖ ≤ √(natGenerator v : ℝ) ∧ ‖β‖ ≤ √(natGenerator v : ℝ) := by
  have hp := prime_natGenerator v
  have h1 : (1 : ℝ) ≤ √(natGenerator v : ℝ) := by
    rw [Real.one_le_sqrt]; exact_mod_cast hp.one_lt.le
  have hcard := ZInQ.Literature.natCard_residueField v
  unfold localPolynomial
  split_ifs with hg hs hm
  · have : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))
    have := (hasGoodReduction_iff_isElliptic_reduction _).mp hg
    have hH := hB _ (((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ))
    rw [Fintype.card_eq_nat_card, hcard] at hH
    set N := Nat.card (((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point
    have hsq : (((natGenerator v : ℤ) + 1 - N : ℤ) : ℝ) ^ 2 ≤ 4 * ((natGenerator v : ℤ) : ℝ) := by
      have h2 := abs_le.mp hH
      have hs0 : 0 ≤ √(natGenerator v : ℝ) := Real.sqrt_nonneg _
      have hss := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (natGenerator v))
      push_cast
      nlinarith [h2.1, h2.2]
    obtain ⟨α, β, hs1, hp1, hα, hβ⟩ := exists_roots_of_sq_le _ _ hsq
    refine ⟨_, _, α, β, ?_, hs1, hp1, ?_, ?_⟩
    · rw [hcard]
    · simpa using hα
    · simpa using hβ
  · refine ⟨1, 0, 1, 0, by simp, by simp, by simp, by simpa using h1, by simp⟩
  · refine ⟨-1, 0, -1, 0, by simp, by simp, by simp, by simpa using h1, by simp⟩
  · refine ⟨0, 0, 0, 0, by simp, by simp, by simp, by simp, by simp⟩

theorem sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : √(x ^ k) = √x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

/-- **`|a_{p^k}| ≤ (k + 1) p^{k/2}`** given Hasse's bound. PROVED from `HasseBound`. -/
theorem norm_lcoeff_prime_pow_le (hB : HasseBound) (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (k : ℕ) :
    ‖ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff E (natGenerator v ^ k)‖ ≤
      (k + 1) * √(natGenerator v : ℝ) ^ k := by
  obtain ⟨a, b, α, β, hP, hs, hp, hα, hβ⟩ := exists_localPolynomial_roots hB E v
  rw [ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff, ZInQ.Manuscript.RC.TwistDictionary.LFunction_prime_pow,
    hP]
  exact norm_coeff_invOfUnit_le a b α β hs hp hα hβ k

/-- **`|a_n| ≤ d(n) √n`** given Hasse's bound. PROVED from `HasseBound`. -/
theorem norm_lcoeff_le (hB : HasseBound) (E : WeierstrassCurve ℚ) (n : ℕ) :
    ‖ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff E n‖ ≤ (ArithmeticFunction.sigma 0 n : ℝ) * √(n : ℝ) := by
  have hmul := ZInQ.Literature.isMultiplicative_LFunction E
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp [ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff]
  | one =>
    simp [ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff, hmul.map_one]
  | prime_pow p k hp hk =>
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨v, rfl⟩ := ZInQ.Literature.exists_natGenerator_eq p
    rw [sigma_zero_apply_prime_pow hp, Nat.cast_pow, sqrt_pow_eq _ (Nat.cast_nonneg _)]
    push_cast
    exact norm_lcoeff_prime_pow_le hB E v k
  | coprime m n hm hn hmn ihm ihn =>
    rw [ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff, hmul.map_mul_of_coprime hmn, Int.cast_mul,
      norm_mul, isMultiplicative_sigma.map_mul_of_coprime hmn, Nat.cast_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _)]
    calc ‖((E.LFunction m : ℤ) : ℂ)‖ * ‖((E.LFunction n : ℤ) : ℂ)‖
        ≤ ((ArithmeticFunction.sigma 0 m : ℝ) * √(m : ℝ)) * ((ArithmeticFunction.sigma 0 n : ℝ) * √(n : ℝ)) :=
          mul_le_mul ihm ihn (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- **`HasseConvergence` from Hasse's bound** (PROVED reduction). -/
theorem hasseConvergence_of_hasseBound (hB : HasseBound) :
    ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence := by
  intro E _ s hs
  set t : ℂ := s - 1 / 2
  have hts : t.re = s.re - 1 / 2 := by
    simp only [t, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  have ht : 1 < t.re := by rw [hts]; linarith
  set d : ArithmeticFunction ℂ :=
    ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
  have hd : LSeriesSummable (fun n => d n) t := by
    have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
        ArithmeticFunction ℂ) n) t := by
      have := LSeriesSummable_zeta_iff.mpr ht
      convert this using 1
      funext n
      exact natCoe_apply
    have e : d = ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) := by
      simp only [d]
      rw [← natCoe_mul, ← ArithmeticFunction.zeta_mul_pow_eq_sigma,
        ArithmeticFunction.pow_zero_eq_zeta]
    rw [e]
    exact ArithmeticFunction.LSeriesSummable_mul hz hz
  have hdn : ∀ n : ℕ, d n = ((ArithmeticFunction.sigma 0 n : ℕ) : ℂ) := fun n => natCoe_apply
  refine Summable.of_norm_bounded (summable_norm_iff.mpr hd) fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ite_eq_right hn, ite_eq_right hn, hdn, Complex.norm_natCast]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb := norm_lcoeff_le hB E n
  have e1 : (n : ℝ) ^ s.re = (n : ℝ) ^ t.re * √(n : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0, hts]; ring_nf
  rw [e1, div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖ZInQ.Manuscript.RC.PrintsAnalytic.lcoeff E n‖ * (n : ℝ) ^ t.re
      ≤ ((ArithmeticFunction.sigma 0 n : ℝ) * √(n : ℝ)) * (n : ℝ) ^ t.re :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

/-- **`HasseConvergence` from Hasse's bound** (PROVED reduction; the GLUE becomes the statement
`HasseBound`, itself PROVED in `WeilIsogeny/HasseProof.lean`). -/
theorem hasseConvergence_proof (hB : HasseBound) :
    ZInQ.Manuscript.RC.PrintsAnalytic.HasseConvergence :=
  hasseConvergence_of_hasseBound hB

end ZInQ.Contrib.CloudB3RC53.Hasse
