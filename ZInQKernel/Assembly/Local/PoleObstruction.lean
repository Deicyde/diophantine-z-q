import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Multiplication.Certificate.Parity

/-!
# The one-sided pole obstruction

Blueprint: `multiplication/pole-obstruction.md` (Lemma 5.1), in the form used by the
divisibility lemma: if `B ≠ 0` and `Φ(B)`, then for every prime `p ∤ 2730` the valuation
`v_p(B)` is not negative and odd.

A rational zero of the pole polynomial with input `B ≠ 0` makes its sum of squares vanish, so
it is a solution of the Route K witness system `ZInQ.Mult.poleSystem`, and the statement is
`ZInQ.Mult.poleSystem_no_negative_odd_valuation` (the `x + ℓ` copy of upstream's lemma).
-/

namespace ZInQ.Assembly

theorem four_sq_eq_zero {a b c d : ℚ} (ha : 0 ≤ a) (h : a + b ^ 2 + c ^ 2 + d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hb := sq_nonneg b
  have hc := sq_nonneg c
  have hd := sq_nonneg d
  refine ⟨by linarith, ?_, ?_, ?_⟩ <;> apply pow_eq_zero_iff (n := 2) (by norm_num) |>.mp <;>
    linarith

/-- **The one-sided pole obstruction.** If `B ≠ 0` and `Φ(B)`, then for every prime `p ∤ 2730`,
`v_p(B)` is not negative and odd. -/
theorem poleSoluble_no_negative_odd {B : ℚ} (hB : B ≠ 0) (hΦ : PoleSoluble B) {p : ℕ}
    (hp : p.Prime) (hp2730 : ¬ p ∣ 2730) :
    ¬ (padicValRat p B < 0 ∧ Odd (padicValRat p B)) := by
  obtain ⟨b, e, z, r₁, r₂, w, h⟩ := hΦ
  exact Mult.poleSystem_no_negative_odd_valuation B _ hB (Mult.poleSystem_of_polePoly_eq_zero hB h)
    p hp hp2730

end ZInQ.Assembly
