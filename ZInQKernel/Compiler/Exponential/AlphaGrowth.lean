import ZInQ.AlphaPowerBounds

/-!
# Growth of the alpha sequence

Blueprint: `compiler/natural/exponential/alpha-growth.md`.

For `b ≥ 2`: `0 ≤ U_n`, `U_n + 1 ≤ U_{n+1}` and `n ≤ U_n`; moreover `c^n ≤ α_{c+1}(n+1)` for
`c ≥ 1`, and `α_b(n+1) ≤ b^n` for `b ≥ 3`. Everything is upstream (`alphaZ_step`,
`alphaZ_ge_index`, `pow_le_alphaZ_succ`, `alphaZ_succ_le_pow`); this module bundles it and adds
monotonicity.
-/

namespace ZInQ.AlphaPower

/-- Growth of the alpha sequence for `b ≥ 2`. -/
theorem alphaZ_growth (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    0 ≤ alphaZ b n ∧ alphaZ b n + 1 ≤ alphaZ b (n + 1) ∧ (n : ℤ) ≤ alphaZ b n :=
  ⟨(alphaZ_step b hb n).1, (alphaZ_step b hb n).2, alphaZ_ge_index b n hb⟩

/-- The exponential bounds: `c^n ≤ α_{c+1}(n+1)` for `c ≥ 1`, and `α_b(n+1) ≤ b^n` for `b ≥ 3`. -/
theorem alphaZ_exponential_bounds (b c n : ℕ) :
    (1 ≤ c → (c : ℤ) ^ n ≤ alphaZ (c + 1) (n + 1)) ∧
      (3 ≤ b → alphaZ b (n + 1) ≤ (b : ℤ) ^ n) :=
  ⟨fun hc => pow_le_alphaZ_succ c n hc, fun hb => alphaZ_succ_le_pow b n hb⟩

theorem alphaZ_nonneg (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : 0 ≤ alphaZ b n :=
  (alphaZ_step b hb n).1

theorem alphaZ_strictMono (b : ℕ) (hb : 2 ≤ b) : StrictMono (alphaZ b) :=
  strictMono_nat_of_lt_succ fun n => alphaZ_succ_strict b n hb

theorem alphaZ_le_of_le (b : ℕ) (hb : 2 ≤ b) {j m : ℕ} (hjm : j ≤ m) :
    alphaZ b j ≤ alphaZ b m :=
  (alphaZ_strictMono b hb).monotone hjm

theorem alphaZ_lt_of_lt (b : ℕ) (hb : 2 ≤ b) {j m : ℕ} (hjm : j < m) :
    alphaZ b j < alphaZ b m :=
  alphaZ_strictMono b hb hjm

theorem alphaZ_pos (b : ℕ) (hb : 2 ≤ b) {n : ℕ} (hn : 0 < n) : 0 < alphaZ b n := by
  have := alphaZ_ge_index b n hb
  omega

end ZInQ.AlphaPower
