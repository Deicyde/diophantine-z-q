import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.Arithmetic
import Mathlib.NumberTheory.FundamentalDiscriminant

/-! The reduction of Fowler, Proposition 2.7, to Proposition 2.6 and the conductor formula. -/

namespace HDec.CMBranch.FowlerArithmetic

private theorem exists_fundamental_factor_aux (a : ℕ) : ∀ Δ : ℤ, Δ.natAbs = a →
    Δ < 0 → (Δ % 4 = 0 ∨ Δ % 4 = 1) →
    ∃ (D : ℤ) (f : ℕ), D < 0 ∧ Int.IsFundamentalDiscr D ∧ 0 < f ∧ Δ = (f : ℤ)^2 * D := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro Δ ha hn hm
    by_cases hfund : Int.IsFundamentalDiscr Δ
    · exact ⟨Δ, 1, hn, hfund, by decide, by simp⟩
    have hbad : ¬ ∀ p : ℕ, p.Prime → ¬ ∃ e : ℤ,
        Δ = (p : ℤ)^2 * e ∧ (e % 4 = 0 ∨ e % 4 = 1) := by
      intro h
      exact hfund (Int.isFundamentalDiscr_iff_forall_prime.mpr ⟨hm, h⟩)
    push Not at hbad
    obtain ⟨p, hp, e, he, hmod⟩ := hbad
    have hen : e < 0 := by
      by_contra! hz
      rw [he] at hn
      exact (not_lt_of_ge (mul_nonneg (sq_nonneg _) hz)) hn
    have habs : a = p^2 * e.natAbs := by
      rw [← ha, he, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    have hp2 := hp.two_le
    have hne : 0 < e.natAbs := Int.natAbs_pos.mpr hen.ne
    have hlt : e.natAbs < a := by
      have hpow : 1 < p ^ 2 := by nlinarith
      rw [habs]
      simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hpow hne
    obtain ⟨D, f, hD, hFD, hf, heq⟩ := ih e.natAbs hlt e rfl hen hmod
    exact ⟨D, p * f, hD, hFD, Nat.mul_pos hp.pos hf, by rw [he, heq]; push_cast; ring⟩

/-- A negative order discriminant is a positive conductor square times a fundamental one. -/
theorem exists_fundamental_factor {Δ : ℤ} (hn : Δ < 0) (hm : Δ % 4 = 0 ∨ Δ % 4 = 1) :
    ∃ (D : ℤ) (f : ℕ), D < 0 ∧ Int.IsFundamentalDiscr D ∧ 0 < f ∧ Δ = (f : ℤ)^2 * D :=
  exists_fundamental_factor_aux Δ.natAbs Δ rfl hn hm

/-- Fowler, Proposition 2.6, in the squared form used in the proof on p. 615. -/
def FundamentalLogBound (h : ℤ → ℕ) : Prop :=
  ∀ D : ℤ, D < 0 → Int.IsFundamentalDiscr D → Real.log |(D : ℝ)| ≤ 42000 * (h D : ℝ)^2

/-- The part of Cox, Theorem 7.24, needed in Fowler's proof.
The unit index is 1 outside `D = -3, -4` and at most 3 in all cases. The local factors
are those in the printed formula with the Kronecker symbol; only its upper bound
by 1 is used, so `symbol` is existential. Positivity is of the fundamental class number. -/
def ConductorFormulaData (h : ℤ → ℕ) : Prop :=
  ∀ (D : ℤ) (f : ℕ), D < 0 → Int.IsFundamentalDiscr D → 0 < f →
    ∃ (u : ℕ) (symbol : ℕ → ℤ), 0 < h D ∧ 0 < u ∧ u ≤ 3 ∧
      (D ≠ -3 → D ≠ -4 → u = 1) ∧ (∀ p ∈ f.primeFactors, symbol p ≤ 1) ∧
      (h ((f : ℤ)^2 * D) : ℝ) * (u : ℝ) =
        (h D : ℝ) * (f : ℝ) * ∏ p ∈ f.primeFactors, (1 - (symbol p : ℝ) / (p : ℝ))

/-- Euler's totient is the lower product obtained by taking each symbol to be 1. -/
private theorem totient_le_product {f : ℕ} {s : ℕ → ℤ} (hs : ∀ p ∈ f.primeFactors, s p ≤ 1) :
    (f.totient : ℝ) ≤ (f : ℝ) * ∏ p ∈ f.primeFactors, (1 - (s p : ℝ) / (p : ℝ)) := by
  have eqR : (f.totient : ℝ) = (f : ℝ) * ∏ p ∈ f.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors f)
    push_cast at hr
    exact hr
  rw [eqR]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg f)
  apply Finset.prod_le_prod₀
  · intro p hp
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
  · intro p hp
    have h : (s p : ℝ) ≤ 1 := by exact_mod_cast hs p hp
    have hd := div_le_div_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) p)
    exact sub_le_sub_left (by simpa [one_div] using hd) _

/-- Proposition 2.7 with the class-number function left explicit for the actual receiver. -/
theorem fowler_bound_from_literature {h : ℤ → ℕ} (hfnd : FundamentalLogBound h)
    (hcox : ConductorFormulaData h) (Δ : ℤ) (hn : Δ < 0) (hm : Δ % 4 = 0 ∨ Δ % 4 = 1)
    (n : ℕ) (hnpos : 0 < n) (hh : h Δ ≤ n) :
    Real.sqrt |(Δ : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) := by
  obtain ⟨D, f, hD, hFD, hf, rfl⟩ := exists_fundamental_factor hn hm
  obtain ⟨u, s, hc, hu, hu3, hu1, hs, heq⟩ := hcox D f hD hFD hf
  have hprod := mul_le_mul_of_nonneg_left (totient_le_product hs) (Nat.cast_nonneg (h D))
  rw [← mul_assoc, ← heq] at hprod
  have htpos := Nat.totient_pos.mpr hf
  have hb : h D * f.totient ≤ h ((f : ℤ)^2 * D) * u := by exact_mod_cast hprod
  have hsmall : f.totient ≤ h D * f.totient := by
    have hc' : 1 ≤ h D := hc
    simpa only [one_mul] using Nat.mul_le_mul_right f.totient hc'
  by_cases hex : D = -3 ∨ D = -4
  · have ht : f.totient ≤ 3 * n := calc
      f.totient ≤ h D * f.totient := hsmall
      _ ≤ h ((f : ℤ)^2 * D) * u := hb
      _ ≤ 3 * n := by rw [mul_comm 3]; exact Nat.mul_le_mul hh hu3
    apply bound_of_small hex hnpos
    calc
      f ≤ 2 * f.totient ^ 2 := le_two_mul_totient_sq f
      _ ≤ 2 * (3 * n) ^ 2 := by gcongr
      _ = 18 * n ^ 2 := by ring
  · push Not at hex
    rw [hu1 hex.1 hex.2, mul_one] at hb
    have ht : f.totient ≤ n := hsmall.trans (hb.trans hh)
    have hmul : h D ≤ h D * f.totient := by
      have htpos' : 1 ≤ f.totient := htpos
      simpa only [mul_one] using Nat.mul_le_mul_left (h D) htpos'
    have hhn : h D ≤ n := hmul.trans (hb.trans hh)
    apply bound_of_log hD ((le_two_mul_totient_sq f).trans (by gcongr))
    exact (hfnd D hD hFD).trans (by gcongr)

end HDec.CMBranch.FowlerArithmetic
