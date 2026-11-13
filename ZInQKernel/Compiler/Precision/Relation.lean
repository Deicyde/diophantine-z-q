import ZInQKernel.Compiler.Precision.Encoding
import ZInQKernel.Compiler.Precision.ZCoordinate
import ZInQKernel.Compiler.Precision.HeightConstant
import ZInQKernel.Model.Generator.InfiniteOrder

/-!
# The precision relation

Blueprint: `compiler/natural/precision/precision-relation.md` and
`compiler/natural/precision/precision-guards.md`.

`accepts c` decodes `c ∈ ℕ⁵` to `(n, κ, a, l, j)` and requires the early tests, admissibility of
`l, a, j`, the closeness test `|r(a, j) - n| < ε_l` and the precision test
`4 ε_l · 4^𝓑(n, κ) < 1`. Given that `P₀` has infinite order, admissibility follows from the early
tests (`accepts_iff_tests`); this uses `genP0_not_isOfFinAddOrder` (`Model/Generator`).
-/

namespace ZInQ.Compiler.Precision

open WeierstrassCurve WeierstrassCurve.Affine

/-- The early tests `n ∉ 𝒞`, `κ ≠ 0`, `a ≥ 1`, `l ≥ 1`, `j = n a`. -/
def EarlyTestsInt (n κ a l j : ℤ) : Prop :=
  n ∉ contacts ∧ κ ≠ 0 ∧ 1 ≤ a ∧ 1 ≤ l ∧ j = n * a

/-- The closeness test `|r(a, j) - n| < ε_l`. -/
def CloseTestInt (n a l j : ℤ) : Prop := |rRatio a j - n| < epsIdx l

/-- The precision test `4 ε_l · 4^𝓑(n, κ) < 1`, that is `4 ε_l < 4^(-𝓑(n, κ))`. -/
def PrecisionTestInt (n κ l : ℤ) : Prop := 4 * epsIdx l * 4 ^ bound n κ < 1

/-- The precision relation on decoded inputs `(n, κ, a, l, j)`. -/
def acceptsInt (n κ a l j : ℤ) : Prop :=
  EarlyTestsInt n κ a l j ∧ (Admissible l ∧ Admissible a ∧ Admissible j) ∧
    CloseTestInt n a l j ∧ PrecisionTestInt n κ l

/-- The early tests of `c ∈ ℕ⁵`, after signed decoding. -/
def EarlyTests (c : Fin 5 → ℕ) : Prop :=
  EarlyTestsInt (dec (c 0)) (dec (c 1)) (dec (c 2)) (dec (c 3)) (dec (c 4))

/-- **The precision relation** `accepts(c)` (`accepts_naturals` of equation (C.4)): the signed
decoding `(n, κ, a, l, j)` of `c` passes the early tests, `l, a, j` are admissible, and
`|r(a, j) - n| < ε_l` and `4 ε_l · 4^𝓑(n, κ) < 1` hold in `ℚ`. -/
def accepts (c : Fin 5 → ℕ) : Prop :=
  acceptsInt (dec (c 0)) (dec (c 1)) (dec (c 2)) (dec (c 3)) (dec (c 4))

theorem accepts_iff (c : Fin 5 → ℕ) :
    accepts c ↔
      (dec (c 0) ∉ contacts ∧ dec (c 1) ≠ 0 ∧ 1 ≤ dec (c 2) ∧ 1 ≤ dec (c 3) ∧
        dec (c 4) = dec (c 0) * dec (c 2)) ∧
      (Admissible (dec (c 3)) ∧ Admissible (dec (c 2)) ∧ Admissible (dec (c 4))) ∧
      |rRatio (dec (c 2)) (dec (c 4)) - dec (c 0)| < epsIdx (dec (c 3)) ∧
      4 * epsIdx (dec (c 3)) * 4 ^ bound (dec (c 0)) (dec (c 1)) < 1 := Iff.rfl

/-- The precision test in the form `4 ε_l < 4^(-𝓑)`. -/
theorem precisionTestInt_iff (n κ l : ℤ) :
    PrecisionTestInt n κ l ↔ 4 * epsIdx l < ((4 : ℚ) ^ bound n κ)⁻¹ := by
  rw [PrecisionTestInt, ← lt_div_iff₀ (by positivity), one_div]

/-! ### Admissibility of nonzero indices -/

/-- If `P₀` has infinite order, every nonzero index is admissible. -/
theorem admissible_of_ne_zero_of (hP : ¬ IsOfFinAddOrder genP0) {k : ℤ} (hk : k ≠ 0) :
    Admissible k := by
  have hne : ∀ m : ℤ, m ≠ 0 → m • genP0 ≠ 0 := fun m hm h =>
    hP (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m, hm, h⟩)
  match hkP : k • genP0 with
  | .zero => exact absurd hkP (hne k hk)
  | .some x y h =>
    refine ⟨x, y, h, hkP, fun hy => ?_⟩
    have h2 : (2 : ℕ) • (Point.some x y h : genCurve.toAffine.Point) = 0 :=
      (shortCurve_two_nsmul_some_eq_zero_iff (A := -genD ^ 2) h).mpr hy
    apply hne (2 * k) (by omega)
    rw [mul_zsmul, hkP, two_zsmul, ← two_nsmul]
    exact h2

/-- If `P₀` has infinite order, an input passing the early tests is accepted exactly when the
closeness and precision tests hold. -/
theorem accepts_iff_tests_of (hP : ¬ IsOfFinAddOrder genP0) (c : Fin 5 → ℕ) (hc : EarlyTests c) :
    accepts c ↔
      CloseTestInt (dec (c 0)) (dec (c 2)) (dec (c 3)) (dec (c 4)) ∧
        PrecisionTestInt (dec (c 0)) (dec (c 1)) (dec (c 3)) := by
  obtain ⟨hn, hκ, ha, hl, hj⟩ := hc
  have hn0 : dec (c 0) ≠ 0 := fun h => hn (by rw [h]; decide)
  refine ⟨fun h => h.2.2, fun h => ⟨⟨hn, hκ, ha, hl, hj⟩, ⟨?_, ?_, ?_⟩, h⟩⟩
  · exact admissible_of_ne_zero_of hP (by omega)
  · exact admissible_of_ne_zero_of hP (by omega)
  · exact admissible_of_ne_zero_of hP (by rw [hj]; exact mul_ne_zero hn0 (by omega))

/-- **Admissibility of nonzero indices**: every `k ≠ 0` is admissible. -/
theorem admissible_of_ne_zero {k : ℤ} (hk : k ≠ 0) : Admissible k :=
  admissible_of_ne_zero_of genP0_not_isOfFinAddOrder hk

/-- An input passing the early tests is accepted exactly when the closeness and precision
tests hold. -/
theorem accepts_iff_tests (c : Fin 5 → ℕ) (hc : EarlyTests c) :
    accepts c ↔
      CloseTestInt (dec (c 0)) (dec (c 2)) (dec (c 3)) (dec (c 4)) ∧
        PrecisionTestInt (dec (c 0)) (dec (c 1)) (dec (c 3)) :=
  accepts_iff_tests_of genP0_not_isOfFinAddOrder c hc

end ZInQ.Compiler.Precision
