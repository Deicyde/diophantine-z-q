import ZInQKernel.Hypotheses.Pole
import ZInQ.PoleValuation

/-!
# The one-sided pole obstruction

Blueprint: `multiplication/pole-obstruction.md` (Lemma 5.1), in the form used by the
divisibility lemma: if `B ≠ 0` and `Φ(B)`, then for every prime `p ∤ 2730` the valuation
`v_p(B)` is not negative and odd.

A rational zero of the pole polynomial with input `B ≠ 0` makes its sum of squares vanish, so
it is a solution of upstream's witness system `ZInQ.ValuationObstruction.poleSystem`, and the
statement is upstream's `poleSystem_no_negative_odd_valuation`.
-/

namespace ZInQ.Assembly

open ZInQ.ValuationObstruction

theorem four_sq_eq_zero {a b c d : ℚ} (ha : 0 ≤ a) (h : a + b ^ 2 + c ^ 2 + d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hb := sq_nonneg b
  have hc := sq_nonneg c
  have hd := sq_nonneg d
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> apply pow_eq_zero_iff (n := 2) (by norm_num) |>.mp <;>
    linarith

/-- A solution of the pole polynomial with input `B ≠ 0` solves the witness system. -/
theorem poleSystem_of_polePoly {B : ℚ} (hB : B ≠ 0) {b : Fin 6 → ℚ} {e z r₁ r₂ w : ℚ}
    (h : polePoly B b e z r₁ r₂ w = 0) : poleSystem B ⟨b, e, z, r₁, r₂, w⟩ := by
  unfold polePoly at h
  obtain ⟨e0, e1, e2, e3⟩ :=
    four_sq_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _) ((mul_eq_zero.mp h).resolve_left hB)
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _] at e0
  exact ⟨fun i => pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (e0 i (Finset.mem_univ i)),
    sub_eq_zero.mp e1, sub_eq_zero.mp e2, sub_eq_zero.mp e3⟩

/-- **The one-sided pole obstruction.** If `B ≠ 0` and `Φ(B)`, then for every prime `p ∤ 2730`,
`v_p(B)` is not negative and odd. -/
theorem poleSoluble_no_negative_odd {B : ℚ} (hB : B ≠ 0) (hΦ : PoleSoluble B) {p : ℕ}
    (hp : p.Prime) (hp2730 : ¬ p ∣ 2730) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  obtain ⟨b, e, z, r₁, r₂, w, h⟩ := hΦ
  exact poleSystem_no_negative_odd_valuation B _ hB (poleSystem_of_polePoly hB h) p hp hp2730

end ZInQ.Assembly
