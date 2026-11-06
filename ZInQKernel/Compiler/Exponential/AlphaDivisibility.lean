import ZInQ.AlphaSquareDivisibilityDraft

/-!
# Divisibility of alpha values

Blueprint: `compiler/natural/exponential/alpha-divisibility.md`.

For `b > 2`: `U_k ∣ U_m ↔ k ∣ m` (`k > 0`; upstream `alphaZ_dvd_iff`), and equation (C.1)
`U_k² ∣ U_m ↔ k U_k ∣ m` (`m > 0`; upstream `alphaZ_sq_dvd_iff`), where for `k = 0` both sides
are false.
-/

namespace ZInQ.AlphaPower

/-- `U_k ∣ U_m ↔ k ∣ m` for `b > 2` and `k > 0`. -/
theorem alphaZ_dvd_alphaZ_iff (b k m : ℕ) (hb : 2 < b) (hk : 0 < k) :
    alphaZ b k ∣ alphaZ b m ↔ k ∣ m :=
  alphaZ_dvd_iff b k m hb hk

/-- Equation (C.1): `U_k² ∣ U_m ↔ k U_k ∣ m` for `b > 2` and `m > 0`. -/
theorem alphaZ_sq_dvd_alphaZ_iff (b k m : ℕ) (hb : 2 < b) (hm : 0 < m) :
    alphaZ b k ^ 2 ∣ alphaZ b m ↔ (k : ℤ) * alphaZ b k ∣ (m : ℤ) :=
  alphaZ_sq_dvd_iff b k m hb hm

/-- For `k = 0` both sides of (C.1) are false. -/
theorem alphaZ_sq_dvd_alphaZ_zero_index (b m : ℕ) (hb : 2 < b) (hm : 0 < m) :
    ¬ alphaZ b 0 ^ 2 ∣ alphaZ b m ∧ ¬ ((0 : ℕ) : ℤ) * alphaZ b 0 ∣ (m : ℤ) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (alphaZ_sq_dvd_alphaZ_iff b 0 m hb hm).mp h
    simp at this
    omega
  · simp at h
    omega

end ZInQ.AlphaPower
