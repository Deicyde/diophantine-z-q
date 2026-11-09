import ZInQ.AlphaLargeOddPair

/-!
# Odd alpha values are unbounded

Blueprint: `compiler/natural/exponential/alpha-large-odd.md`.

For `b > 3` and every `a` there is `k > 0` with `u = α_b(k)` odd, `u > 2a`, and
`t = α_b(k+1)` satisfying `u < t` and `u² + t² = 1 + but` (upstream `alphaZ_large_odd_pair`).
-/

namespace ZInQ.AlphaPower

theorem alphaZ_large_odd (b a : ℕ) (hb : 3 < b) :
    ∃ k : ℕ, 0 < k ∧ Odd (alphaZ b k) ∧ 2 * (a : ℤ) < alphaZ b k ∧
      alphaZ b k < alphaZ b (k + 1) ∧
      alphaZ b k ^ 2 + alphaZ b (k + 1) ^ 2 = 1 + (b : ℤ) * alphaZ b k * alphaZ b (k + 1) := by
  obtain ⟨k, hk, hodd, ha, hlt, hq⟩ := alphaZ_large_odd_pair b a hb
  exact ⟨k, hk, hodd, ha, hlt, by linear_combination hq⟩

end ZInQ.AlphaPower
