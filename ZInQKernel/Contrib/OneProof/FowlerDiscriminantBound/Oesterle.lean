import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.OesterleProduct

/-! Fowler's fundamental-discriminant estimate from Oesterlé and the genus count. -/

namespace HDec.CMBranch.FowlerArithmetic

/-- The finite support in Oesterlé's Theorem 1: all prime divisors except the largest. -/
noncomputable def oesterlePrimes (D : ℤ) : Finset ℕ :=
  if hs : D.natAbs.primeFactors.Nonempty then
    D.natAbs.primeFactors.erase (D.natAbs.primeFactors.max' hs)
  else ∅

private theorem oesterlePrimes_prime {D : ℤ} {p : ℕ} (hp : p ∈ oesterlePrimes D) : p.Prime := by
  unfold oesterlePrimes at hp
  split at hp
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  · exact (Finset.notMem_empty _ hp).elim

private theorem oesterlePrimes_card (D : ℤ) :
    (oesterlePrimes D).card = D.natAbs.primeFactors.card - 1 := by
  unfold oesterlePrimes
  split
  · exact Finset.card_erase_of_mem (Finset.max'_mem _ _)
  · rename_i hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    decide

/-- Oesterlé, Astérisque 121–122, Exp. 631, Theorem 1 p. 310, constant 7000 in §5.1 p. 321. -/
def OesterleEffectiveBound (h : ℤ → ℕ) : Prop :=
  ∀ D : ℤ, D < 0 → Int.IsFundamentalDiscr D →
    (∏ p ∈ oesterlePrimes D, oesterleFactor p) * Real.log |(D : ℝ)| ≤ 7000 * (h D : ℝ)

/-- Genus number divides the class number (Cox 3e, Theorem 6.1(iii)). -/
def GenusDivisibility (h : ℤ → ℕ) : Prop :=
  ∀ D : ℤ, D < 0 → Int.IsFundamentalDiscr D → 2 ^ (D.natAbs.primeFactors.card - 1) ∣ h D

/-- The explicit square-root-log estimate in Fowler, Proposition 2.6. -/
theorem fundamental_log_bound_of_oesterle_genus {h : ℤ → ℕ}
    (ho : OesterleEffectiveBound h) (hg : GenusDivisibility h) (hc : ConductorFormulaData h) :
    FundamentalLogBound h := by
  intro D hD hfund
  by_cases hl : 0 ≤ Real.log |(D : ℝ)|
  · let S := oesterlePrimes D
    let F := ∏ p ∈ S, oesterleFactor p
    obtain ⟨_, _, hpos, _⟩ := hc D 1 hD hfund (by decide)
    have hdiv : 2 ^ S.card ∣ h D := by
      simpa only [S, oesterlePrimes_card] using hg D hD hfund
    have hhN := Nat.le_of_dvd hpos hdiv
    have hh : (2 : ℝ)^S.card ≤ (h D : ℝ) := by exact_mod_cast hhN
    have hprod : (1 : ℝ)/6 ≤ (2:ℝ)^S.card * F :=
      oesterle_product_estimate S (fun _ hp => oesterlePrimes_prime hp)
    have hF : 0 ≤ F := by
      have hp : (0 : ℝ) < (2:ℝ)^S.card := by positivity
      exact nonneg_of_mul_nonneg_right (by linarith) hp
    have hFH : (1 : ℝ)/6 ≤ (h D : ℝ) * F := hprod.trans (mul_le_mul_of_nonneg_right hh hF)
    have hO : F * Real.log |(D : ℝ)| ≤ 7000 * (h D : ℝ) := ho D hD hfund
    have hh' : Real.log |(D : ℝ)| / 6 ≤ 7000 * (h D : ℝ)^2 := calc
      Real.log |(D : ℝ)| / 6 = Real.log |(D : ℝ)| * (1 / 6) := by ring
      _ ≤ Real.log |(D : ℝ)| * ((h D : ℝ) * F) := mul_le_mul_of_nonneg_left hFH hl
      _ = (h D : ℝ) * (F * Real.log |(D : ℝ)|) := by ring
      _ ≤ (h D : ℝ) * (7000 * (h D : ℝ)) := mul_le_mul_of_nonneg_left hO (by positivity)
      _ = 7000 * (h D : ℝ)^2 := by ring
    linarith
  · exact (le_of_not_ge hl).trans (by positivity)

/-- Fowler's full order-discriminant bound from Oesterlé, Gauss and Cox. -/
theorem fowler_bound_from_oesterle_genus_cox {h : ℤ → ℕ}
    (ho : OesterleEffectiveBound h) (hg : GenusDivisibility h) (hc : ConductorFormulaData h)
    (Δ : ℤ) (hn : Δ < 0) (hm : Δ % 4 = 0 ∨ Δ % 4 = 1)
    (n : ℕ) (hnpos : 0 < n) (hh : h Δ ≤ n) :
    Real.sqrt |(Δ : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) :=
  fowler_bound_from_literature (fundamental_log_bound_of_oesterle_genus ho hg hc) hc Δ hn hm n
    hnpos hh

end HDec.CMBranch.FowlerArithmetic
