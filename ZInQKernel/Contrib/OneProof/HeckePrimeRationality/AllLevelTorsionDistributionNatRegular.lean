import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNat
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionTwoRegular
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelUnipotentAverage

/-!
# Degree-`n` distribution of the zero-extended torsion function, for all labels

With the zero extension `reg N a b τ` (`0` when `N` divides both `a` and `b`, the raw torsion
logarithmic derivative otherwise), for positive integers `n`, `N` and all integers `a, b`:
`Σ_{r,s < n} reg (nN) (a + N r) (b + N s) τ = n · reg N a b τ`.

* For admissible `(a, b)` this is the raw degree-`n` distribution.
* For `a = N a'`, `b = N b'` the right side is `0`. The left side is the sum of
  `g(x, y) = reg (nN) (N x) (N y) τ` over a full period of `(x, y)` modulo `n`; the function `g`
  is `n`-periodic in each variable (translation law of the torsion family) and odd
  (`g(-x, -y) = -g(x, y)`, from the `-I` action), so the sum vanishes. Individual admissible
  `n`-torsion values need not vanish for `n > 2`; only the full sum does.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionNat

open TorsionDistributionTwo (reg reg_of_good reg_of_bad)

/-- `reg` is periodic modulo the level in both labels. -/
theorem reg_shift {M : ℕ} (hM : 0 < M) (A B m k : ℤ) (τ : ℍ) :
    reg M (A + M * m) (B + M * k) τ = reg M A B τ := by
  by_cases hg : (M : ℤ) ∣ A ∧ (M : ℤ) ∣ B
  · rw [reg_of_bad hg, reg_of_bad ⟨dvd_add hg.1 (dvd_mul_right _ _), dvd_add hg.2 (dvd_mul_right _ _)⟩]
  · have hg' : ¬ ((M : ℤ) ∣ A + M * m ∧ (M : ℤ) ∣ B + M * k) :=
      (AllLevelForms.good_shift (N := M) (a := A) (b := B) m k).mpr hg
    rw [reg_of_good hg, reg_of_good hg']
    exact AllLevelForms.F_shift hM hg m k τ

/-- `reg` is odd in the label. -/
theorem reg_neg {M : ℕ} (hM : 0 < M) (A B : ℤ) (τ : ℍ) :
    reg M (-A) (-B) τ = -reg M A B τ := by
  by_cases hg : (M : ℤ) ∣ A ∧ (M : ℤ) ∣ B
  · rw [reg_of_bad hg, reg_of_bad ⟨(dvd_neg).mpr hg.1, (dvd_neg).mpr hg.2⟩, neg_zero]
  · have hg' : ¬ ((M : ℤ) ∣ -A ∧ (M : ℤ) ∣ -B) := by
      rintro ⟨h1, h2⟩; exact hg ⟨(dvd_neg).mp h1, (dvd_neg).mp h2⟩
    rw [reg_of_good hg, reg_of_good hg']
    exact AllLevelTraceTwoZeroConvention.raw_neg M hM A B hg τ

/-- A full-period sum of an `n`-periodic function is invariant under negation of the argument. -/
theorem sum_range_neg {Mo : Type*} [AddCommGroup Mo] {n : ℕ} (h : ℤ → Mo)
    (hper : ∀ m, h (m + n) = h m) :
    ∑ j ∈ Finset.range n, h (-(j : ℤ)) = ∑ j ∈ Finset.range n, h j := by
  rw [← Finset.sum_range_reflect (fun j : ℕ => h (-(j : ℤ))) n]
  have hc : ∀ j ∈ Finset.range n, h (-((n - 1 - j : ℕ) : ℤ)) = h ((j : ℤ) + 1) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : -((n - 1 - j : ℕ) : ℤ) + n = (j : ℤ) + 1 := by omega
    rw [← hper, e]
  rw [Finset.sum_congr rfl hc]
  exact AllLevelAverage.sum_range_shift (N := n) h hper 1

/-- The vanishing of the full-period sum at an inadmissible image. -/
theorem reg_sum_bad (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a' b' : ℤ) :
    ∑ r : Fin n, ∑ s : Fin n,
      reg (n * N) (N * a' + N * ((r : ℕ) : ℤ)) (N * b' + N * ((s : ℕ) : ℤ)) τ = 0 := by
  have hnN : 0 < n * N := Nat.mul_pos hn hN
  set g : ℤ → ℤ → ℂ := fun x y => reg (n * N) (N * x) (N * y) τ with hg
  have hperx : ∀ x y : ℤ, g (x + n) y = g x y := by
    intro x y
    simp only [hg]
    rw [show (N : ℤ) * (x + n) = N * x + ((n * N : ℕ) : ℤ) * 1 by push_cast; ring,
      show (N : ℤ) * y = N * y + ((n * N : ℕ) : ℤ) * 0 by ring, reg_shift hnN]
    rw [show (N : ℤ) * y + ((n * N : ℕ) : ℤ) * 0 = N * y by ring]
  have hpery : ∀ x y : ℤ, g x (y + n) = g x y := by
    intro x y
    simp only [hg]
    rw [show (N : ℤ) * (y + n) = N * y + ((n * N : ℕ) : ℤ) * 1 by push_cast; ring,
      show (N : ℤ) * x = N * x + ((n * N : ℕ) : ℤ) * 0 by ring, reg_shift hnN]
    rw [show (N : ℤ) * x + ((n * N : ℕ) : ℤ) * 0 = N * x by ring]
  have hodd : ∀ x y : ℤ, g (-x) (-y) = -g x y := by
    intro x y
    simp only [hg]
    rw [show (N : ℤ) * -x = -(N * x) by ring, show (N : ℤ) * -y = -(N * y) by ring,
      reg_neg hnN]
  have hterm : ∀ r s : Fin n,
      reg (n * N) (N * a' + N * ((r : ℕ) : ℤ)) (N * b' + N * ((s : ℕ) : ℤ)) τ =
        g (((r : ℕ) : ℤ) + a') (((s : ℕ) : ℤ) + b') := by
    intro r s
    simp only [hg]
    rw [show (N : ℤ) * a' + N * ((r : ℕ) : ℤ) = N * (((r : ℕ) : ℤ) + a') by ring,
      show (N : ℤ) * b' + N * ((s : ℕ) : ℤ) = N * (((s : ℕ) : ℤ) + b') by ring]
  simp_rw [hterm]
  have hinner : ∀ x : ℤ, ∑ s : Fin n, g x (((s : ℕ) : ℤ) + b') =
      ∑ s ∈ Finset.range n, g x (s : ℤ) := by
    intro x
    rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => g x ((s : ℤ) + b')) n]
    exact AllLevelAverage.sum_range_shift (N := n) (g x) (hpery x) b'
  simp_rw [hinner]
  set G : ℤ → ℂ := fun x => ∑ s ∈ Finset.range n, g x (s : ℤ) with hG
  have hGper : ∀ x, G (x + n) = G x := fun x => by
    simp only [hG, hperx]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => G ((r : ℤ) + a')) n,
    AllLevelAverage.sum_range_shift (N := n) G hGper a']
  set T := ∑ r ∈ Finset.range n, G (r : ℤ) with hT
  have hneg : ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, g (-(r : ℤ)) (-(s : ℤ)) = T := by
    have h1 : ∀ r : ℕ, ∑ s ∈ Finset.range n, g (-(r : ℤ)) (-(s : ℤ)) = G (-(r : ℤ)) := by
      intro r
      exact sum_range_neg (g (-(r : ℤ))) (hpery _)
    simp_rw [h1]
    exact sum_range_neg G hGper
  have hneg' : ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n, g (-(r : ℤ)) (-(s : ℤ)) = -T := by
    simp_rw [hodd]
    rw [hT]
    simp only [hG, Finset.sum_neg_distrib]
  have : T = -T := hneg.symm.trans hneg'
  linear_combination this / 2

/-- **Degree-`n` distribution of the zero-extended torsion function, for all integer labels.** -/
theorem reg_distribution_nat (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a b : ℤ) :
    ∑ r : Fin n, ∑ s : Fin n, reg (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      (n : ℂ) * reg N a b τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := hg
    rw [reg_of_bad ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, mul_zero]
    exact reg_sum_bad n N hn hN τ a' b'
  · rw [reg_of_good hg]
    have hterm : ∀ r s : Fin n,
        reg (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
          Torsion.torsionLogDerivative (n * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ :=
      fun r s => reg_of_good (good_preimage hg r s) τ
    simp_rw [hterm]
    exact distribution_nat n N hn hN τ a b hg

end ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionNat
