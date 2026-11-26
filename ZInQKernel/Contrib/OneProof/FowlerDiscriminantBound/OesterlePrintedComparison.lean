import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ActualReadings
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-! Comparison with the field quantities in Oesterlé, Exposé 631, Theorem 1 and §1.1. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField
open scoped NumberField

/-- The greatest prime is excluded by requiring a strictly larger prime divisor. -/
theorem mem_oesterlePrimes_iff {D : ℤ} (hD : D ≠ 0) (p : ℕ) :
    p ∈ oesterlePrimes D ↔
      p.Prime ∧ p ∣ D.natAbs ∧ ∃ q : ℕ, q.Prime ∧ q ∣ D.natAbs ∧ p < q := by
  classical
  have hn : D.natAbs ≠ 0 := by omega
  have hm (q : ℕ) : q ∈ D.natAbs.primeFactors ↔ q.Prime ∧ q ∣ D.natAbs := by
    simp [Nat.mem_primeFactors, hn]
  unfold oesterlePrimes
  split
  · rename_i hs
    rw [Finset.mem_erase]
    constructor
    · rintro ⟨hne, hp⟩
      exact ⟨(hm p).mp hp |>.1, (hm p).mp hp |>.2, _,
        (hm _).mp (Finset.max'_mem _ hs) |>.1,
        (hm _).mp (Finset.max'_mem _ hs) |>.2,
        lt_of_le_of_ne (Finset.le_max' _ _ hp) hne⟩
    · rintro ⟨hp, hd, q, hq, hqd, hpq⟩
      exact ⟨ne_of_lt (hpq.trans_le (Finset.le_max' _ _ ((hm q).mpr ⟨hq, hqd⟩))),
        (hm p).mpr ⟨hp, hd⟩⟩
  · rename_i hs
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨hp, hd, -⟩
    exact hs ⟨p, (hm p).mpr ⟨hp, hd⟩⟩

/-- The local factor uses the real floor, including when the square root is integral. -/
theorem oesterleFactor_eq_floor (p : ℕ) :
    oesterleFactor p = 1 - (⌊2 * Real.sqrt (p : ℝ)⌋ : ℝ) / ((p : ℝ) + 1) := by
  have hs : Real.sqrt ((4 * p : ℕ) : ℝ) = 2 * Real.sqrt (p : ℝ) := by
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [← hs, Real.floor_real_sqrt_eq_nat_sqrt]
  simp [oesterleFactor]

/-- A positive magnitude whose negative is the discriminant of the ring of integers. -/
theorem exists_oesterle_discriminant (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ d : ℕ, 0 < d ∧ -(d : ℤ) = discr K := by
  have hdim := IsTotallyComplex.finrank (K := K)
  rw [hK] at hdim
  have hnc : InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hsign := sign_discr K
  rw [hnc] at hsign
  norm_num at hsign
  exact ⟨(discr K).natAbs, by omega, by omega⟩

/-- The printed inequality, with the actual ideal-class cardinal and the positive magnitude
of an integral-basis discriminant, is equivalent to the input in the field endpoint. -/
theorem oesterleFieldBound_iff_printed (K : Type*) [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ (𝓞 K))
    (d : ℕ) (hd : -(d : ℤ) = Algebra.discr ℤ b) :
    OesterleFieldBound K ↔
      (∏ p ∈ d.primeFactors.filter (fun p => ∃ q ∈ d.primeFactors, p < q),
        (1 - (⌊2 * Real.sqrt (p : ℝ)⌋ : ℝ) / ((p : ℝ) + 1))) * Real.log (d : ℝ) ≤
      7000 * (Nat.card (ClassGroup (𝓞 K)) : ℝ) := by
  classical
  have hD : -(d : ℤ) = discr K := hd.trans (NumberField.discr_eq_discr K b)
  have hD0 := discr_ne_zero K
  have hs : d.primeFactors.filter (fun p => ∃ q ∈ d.primeFactors, p < q) =
      oesterlePrimes (discr K) := by
    ext p
    rw [mem_oesterlePrimes_iff hD0, ← hD]
    have hn : d ≠ 0 := by omega
    simp [Nat.mem_primeFactors, hn, and_assoc]
  rw [hs]
  have hn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  simp only [OesterleFieldBound, oesterleFactor_eq_floor, ← hD, Int.cast_neg, Int.cast_natCast,
    abs_neg, abs_of_nonneg hn, NumberField.classNumber, Nat.card_eq_fintype_card]

end HDec.CMBranch.FowlerArithmetic
