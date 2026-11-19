import ZInQKernel.Contrib.OneProof.RC.O12Theta.Source

/-! The valuation reading on a tested squarefree coefficient: compare with
the phase-removed integer representative before reducing (tex 2081–2086,
2538, 9675–9704). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open ZInQ.Manuscript.RC.Odd ThetaCoeff
open scoped Classical

variable {O K : Type} [CommRing O] [IsDomain O] [CharZero O]
  [Field K] [CharZero K] [Algebra O K]
variable {m : Ideal O} {M : ℕ}

private theorem residue_two (h2 : (2 : O) ∈ m) : (2 : O ⧸ m) = 0 := by
  simpa only [map_ofNat] using (Ideal.Quotient.eq_zero_iff_mem.mpr h2 :
    Ideal.Quotient.mk m (2 : O) = 0)

theorem residue_congr (h2 : (2 : O) ∈ m) {b c : O}
    (h : (2 : O) ∣ b - c) : Ideal.Quotient.mk m b = Ideal.Quotient.mk m c := by
  obtain ⟨d, hd⟩ := h
  rw [← sub_eq_zero, ← map_sub, hd, map_mul, map_ofNat, residue_two h2, zero_mul]

/-- A permitted phase has residue one at the chosen place above two. -/
theorem phase_residue (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) {ζ : O}
    (hζ : ∃ k : ℕ, ζ ^ (2 ^ k : ℕ) = 1) : Ideal.Quotient.mk m ζ = 1 := by
  letI : m.IsPrime := hm.isPrime
  obtain ⟨k, hk⟩ := hζ
  let z := Ideal.Quotient.mk m ζ
  have hz : z ^ (2 ^ k : ℕ) = 1 := by
    rw [← map_pow, hk, map_one]
  change z = 1
  clear hk
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    apply ih
    have hs : (z ^ (2 ^ k : ℕ)) ^ 2 = 1 ^ 2 := by
      rw [← pow_mul, ← pow_succ, hz, one_pow]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact h
    · rw [h]
      apply neg_eq_iff_add_eq_zero.mpr
      simpa only [← two_mul, mul_one] using residue_two h2

/-- The residue of a normalized coefficient is the valuation symbol if the
undivided lift agrees at precision `M` with a permitted phase times the
integer used in the valuation. The depth assumption is on that integer. -/
theorem source_symbol_on_filter (hinj : Function.Injective (algebraMap O K))
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) {e : ℤ} (he : e < (M : ℤ))
    {x b ζ : O} {a : ℤ} (hζ : ∃ k : ℕ, ζ ^ (2 ^ k : ℕ) = 1)
    (hrep : stageReduction O M x = stageReduction O M (ζ * (a : O)))
    (ha : (e : WithTop ℤ) ≤ vZ a)
    (hb : algebraMap O K b = (2 : K) ^ (-e) * algebraMap O K x) :
    Ideal.Quotient.mk m b = if vZ a = (e : WithTop ℤ) then 1 else 0 := by
  by_cases he0 : 0 ≤ e
  · let k := e.toNat
    have hk : (k : ℤ) = e := Int.toNat_of_nonneg he0
    obtain ⟨c, hc⟩ := (two_pow_dvd_iff_le_vZ a k).mpr (by rwa [hk])
    have hscale : algebraMap O K (ζ * (c : O)) =
        (2 : K) ^ (-e) * algebraMap O K (ζ * (a : O)) := by
      simp only [map_mul, map_intCast, hc, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, map_pow, map_ofNat]
      rw [mul_left_comm ((2 : K) ^ (-e)), ← mul_assoc ((2 : K) ^ (-e)),
        ← zpow_natCast, hk, ← zpow_add₀ (by norm_num : (2 : K) ≠ 0), neg_add_cancel, zpow_zero,
        one_mul]
    rw [residue_congr h2 (normalized_congr hinj he hrep hb hscale), map_mul,
      phase_residue hm h2 hζ, one_mul, map_intCast]
    have hd : (2 : ℤ) ∣ c ↔ ((e + 1 : ℤ) : WithTop ℤ) ≤ vZ a := by
      rw [← hk, ← Int.natCast_succ, ← two_pow_dvd_iff_le_vZ, hc, pow_succ]
      exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).symm
    have hv : vZ a = (e : WithTop ℤ) ↔ ¬ (2 : ℤ) ∣ c := by
      rw [hd]
      by_cases ha0 : a = 0
      · rw [ha0]
        simp [vZ]
      · rw [vZ_of_ne_zero ha0, WithTop.coe_eq_coe, WithTop.coe_le_coe]
        have hl : e ≤ (padicValInt 2 a : ℤ) := by
          simpa only [vZ_of_ne_zero ha0, WithTop.coe_le_coe] using ha
        omega
    rcases Int.even_or_odd' c with ⟨d, hd' | hd'⟩
    · have h : (2 : ℤ) ∣ c := ⟨d, hd'⟩
      rw [if_neg (fun hv' => hv.mp hv' h), hd', Int.cast_mul, Int.cast_ofNat, residue_two h2, zero_mul]
    · have h : ¬ (2 : ℤ) ∣ c := by
        rintro ⟨a, ha⟩
        omega
      rw [if_pos (hv.mpr h), hd', Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one,
        residue_two h2, zero_mul, zero_add]
  · have hv : vZ a ≠ (e : WithTop ℤ) := by
      intro h
      have hl := (two_pow_dvd_iff_le_vZ a 0).mp (by simp)
      rw [h, WithTop.coe_le_coe] at hl
      omega
    have hk : ((-e).toNat : ℤ) = -e := Int.toNat_of_nonneg (by omega)
    have hb' : b = (2 : O) ^ (-e).toNat * x := by
      apply hinj
      rw [hb, map_mul, map_pow, map_ofNat, ← zpow_natCast, hk]
    rw [if_neg hv, hb', map_mul, map_pow, map_ofNat, residue_two h2,
      zero_pow (by omega), zero_mul]

/-- The off-support vanishing at stage precision gives a zero normalized
residue whenever the test fits within that precision. -/
theorem source_symbol_off_support (hinj : Function.Injective (algebraMap O K))
    (h2 : (2 : O) ∈ m) {e : ℤ} (he : e < (M : ℤ))
    {x b : O} (hx : stageReduction O M x = 0)
    (hb : algebraMap O K b = (2 : K) ^ (-e) * algebraMap O K x) :
    Ideal.Quotient.mk m b = 0 := by
  have h := normalized_congr hinj he (y := 0) (c := 0) (by simpa using hx) hb (by simp)
  simpa using residue_congr h2 h


end ZInQ.Manuscript.RC.O12Theta
