import ZInQKernel.Multiplication.Completeness.SlopeCompleteness
import ZInQKernel.Multiplication.Completeness.PatternSlopes
import ZInQKernel.Multiplication.Completeness.TwoSlope

/-!
# The mathematical core of completeness

For a true triple `(n₁, n₂, n₃) = (a, b, ab)`: every integer is a sum of three slopes satisfying
the slope predicate (the slope representation `SlopeRepresentation`, from 22P or 22P₂, and slope
completeness), and the abscissa coordinates of each `[n_i]P₀` are `a_{ij}/b_i` with integers
`a_{ij}` and `b_i ≥ 1`. These are the witnesses of the height certificate.
-/

namespace ZInQ.Mult

/-- Every integer is a sum of three slopes satisfying `Slope(·, ℓ₀; c_*, c_* n₁, c_* n₂, c_* n₁n₂)`. -/
theorem slopes_of_int (hPC : PoleCompleteness) (h22 : SlopeRepresentation)
    (n₁ n₂ A : ℤ) :
    ∃ t : Fin 3 → ℚ, ∑ l, t l = A ∧
      ∀ l, SlopePred (t l) Syntax.ell (certShifts ![n₁, n₂, n₁ * n₂]) := by
  obtain ⟨t, hsum, hgood⟩ := h22 A
  exact ⟨t, hsum, fun l => slope_complete hPC n₁ n₂ (hgood l)⟩

/-- Two rationals have a common denominator `b ≥ 1`. -/
theorem exists_common_den (x y : ℚ) :
    ∃ b : ℕ, 0 < b ∧ ∃ a₀ a₁ : ℤ, (b : ℚ) * x = a₀ ∧ (b : ℚ) * y = a₁ := by
  refine ⟨x.den * y.den, Nat.mul_pos x.den_pos y.den_pos, x.num * y.den, y.num * x.den, ?_, ?_⟩
  · push_cast
    rw [mul_comm (x.den : ℚ), mul_assoc, Rat.den_mul_eq_num, mul_comm]
  · push_cast
    rw [mul_assoc, Rat.den_mul_eq_num, mul_comm]

/-- **The witnesses of the height certificate for a true triple.** With `n = (a, b, ab)` there
are integers `b_i ≥ 1` and `a_{ij}` with `b_i x_{ij} = a_{ij}`, where `x_{i0}, x_{i1}` are the
coordinates `1, 2` of the code `ι(n_i)`, and each of the nine integers `a_{ij}, b_i` is a sum of
three slopes satisfying the slope predicate. -/
theorem completeness_core (hPC : PoleCompleteness) (h22 : SlopeRepresentation)
    (a b : ℤ) :
    ∃ (B : Fin 3 → ℕ) (A : Fin 3 → Fin 2 → ℤ),
      (∀ i, 0 < B i) ∧
      (∀ i, (B i : ℚ) * iota (![a, b, a * b] i) 1 = A i 0 ∧
        (B i : ℚ) * iota (![a, b, a * b] i) 2 = A i 1) ∧
      (∀ i k, ∃ t : Fin 3 → ℚ, ∑ l, t l = A i k ∧
        ∀ l, SlopePred (t l) Syntax.ell (certShifts ![a, b, a * b])) ∧
      (∀ i, ∃ t : Fin 3 → ℚ, ∑ l, t l = B i ∧
        ∀ l, SlopePred (t l) Syntax.ell (certShifts ![a, b, a * b])) := by
  choose B hB A₀ A₁ hA₀ hA₁ using fun i : Fin 3 =>
    exists_common_den (iota (![a, b, a * b] i) 1) (iota (![a, b, a * b] i) 2)
  refine ⟨B, fun i => ![A₀ i, A₁ i], hB, fun i => ⟨hA₀ i, hA₁ i⟩, fun i k => ?_, fun i => ?_⟩
  · obtain ⟨t, ht, hs⟩ := slopes_of_int hPC h22 a b (![A₀ i, A₁ i] k)
    exact ⟨t, ht, hs⟩
  · obtain ⟨t, ht, hs⟩ := slopes_of_int hPC h22 a b (B i)
    exact ⟨t, by rw [ht]; simp, hs⟩

end ZInQ.Mult
