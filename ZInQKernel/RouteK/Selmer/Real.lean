import ZInQKernel.RouteK.Selmer.Covering

/-!
# The real place

`docs/research/nt-prop0.md` §2.2, Lemma ∞: for `d > 0` and `a, b ≠ 0`, the covering `D_{a,b}` is
soluble over `ℝ` iff `a` and `b` have the same sign. This is row `(R)`, `a₀ = b₀`.
-/

namespace ZInQ.RouteK.Selmer

/-- **Lemma ∞** (nt-prop0 §2.2). -/
theorem loc_real_iff {d a b : ℝ} (hd : 0 < d) (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℝ d a b ↔ (0 < a ↔ 0 < b) := by
  constructor
  · rintro (⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩)
    · rw [Real.isSquare_iff] at hsa hsb
      exact iff_of_true (lt_of_le_of_ne hsa (Ne.symm ha)) (lt_of_le_of_ne hsb (Ne.symm hb))
    rw [Real.isSquare_iff] at h₁ h₂ h₃
    have e₁ : x = x / a * a := by field_simp
    have e₂ : x - d = (x - d) / b * b := by field_simp
    have e₃ : x + d = (x + d) / (a * b) * (a * b) := by field_simp
    rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
    · exact iff_of_false (not_lt.mpr ha'.le) (not_lt.mpr hb'.le)
    · exfalso
      have : x ≤ 0 := by rw [e₁]; exact mul_nonpos_of_nonneg_of_nonpos h₁ ha'.le
      have : 0 ≤ x - d := by rw [e₂]; exact mul_nonneg h₂ hb'.le
      linarith
    · exfalso
      have : 0 ≤ x := by rw [e₁]; exact mul_nonneg h₁ ha'.le
      have : x + d ≤ 0 := by
        rw [e₃]; exact mul_nonpos_of_nonneg_of_nonpos h₃ (mul_neg_of_pos_of_neg ha' hb').le
      linarith
    · exact iff_of_true ha' hb'
  · intro h
    rcases ha.lt_or_gt with ha' | ha'
    · have hb' : b < 0 := lt_of_le_of_ne (not_lt.mp fun hb' => (not_lt.mpr ha'.le) (h.mpr hb')) hb
      refine Or.inr ⟨0, by simp, ?_, ?_⟩ <;> rw [Real.isSquare_iff]
      · rw [zero_sub, neg_div]; exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos hd.le hb'.le)
      · rw [zero_add]; exact div_nonneg hd.le (mul_nonneg_of_nonpos_of_nonpos ha'.le hb'.le)
    · have hb' : 0 < b := h.mp ha'
      refine Or.inr ⟨d, ?_, by simp, ?_⟩ <;> rw [Real.isSquare_iff]
      · exact div_nonneg hd.le ha'.le
      · exact div_nonneg (by linarith) (mul_pos ha' hb').le

/-- **Lemma ∞** for integer pairs, the form `Sel2` uses. -/
theorem loc_real_iff_int {d : ℕ} (hd : d ≠ 0) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℝ d a b ↔ (0 < a ↔ 0 < b) := by
  rw [loc_real_iff (by exact_mod_cast Nat.pos_of_ne_zero hd) (by exact_mod_cast ha)
    (by exact_mod_cast hb), Int.cast_pos, Int.cast_pos]

end ZInQ.RouteK.Selmer
