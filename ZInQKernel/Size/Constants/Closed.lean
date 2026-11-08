import Mathlib

/-!
# Closed numerical comparisons

Blueprint: `size/constants/closed-comparisons.md`.

The closed comparisons used by the symbolic estimates of the size chapter, between explicit
natural numbers of at most `9011` binary digits. None of the astronomical constants occurs.
Each item is decided by the kernel with its GMP `Nat` operations; `exponentiation.threshold`
only lifts the elaborator's safeguard against large literal powers.
-/

namespace ZInQ.Size

set_option exponentiation.threshold 4700 in
/-- Item 1: the exponents of `N_s` and `ℓ`. -/
theorem closed_comparisons_1 :
    433 + 22 * 2 ^ 4608 < 2 ^ 4613 ∧ 4 + 1262628 + 16104 * 2 ^ 4608 < 2 ^ 4623 ∧
      1262628 = 433 * 2916 ∧ 16104 = 22 * 732 := by
  decide

set_option exponentiation.threshold 4700 in
/-- Item 2: the exponent of `c_*`. -/
theorem closed_comparisons_2 : 2 + 10 * 2 ^ 4613 < 2 ^ 4617 := by
  decide

set_option exponentiation.threshold 9100 in
/-- Item 3: `R = D` and the upper bound on `D`. -/
theorem closed_comparisons_3 : 10 ^ 12 < 2 ^ 40 ∧ 2250 + 2 ^ 9009 < 2 ^ 9010 := by
  decide

/-- Item 4: the linear part of `C_cm`. -/
theorem closed_comparisons_4 : 4096 * 85033 < 2 ^ 29 := by
  decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 700 in
/-- Item 5: the prefactor and the exponent coefficient of the closed form of `T`. -/
theorem closed_comparisons_5 :
    (96 * 10 ^ 13) ^ 13 < 2 ^ 650 ∧ 2210 * 116064000000 ^ 2 < 2 ^ 86 := by
  decide

/-- Item 6: the base cases of the division polynomials. -/
theorem closed_comparisons_6 :
    11243 + 2 * 7950 = 27143 ∧
      3 * 3 ^ 4 + 6 * 27143 * 3 ^ 2 + 27143 ^ 2 < 2 ^ 30 ∧
      2 * (3 ^ 6 + 5 * 27143 * 3 ^ 4 + 5 * 27143 ^ 2 * 3 ^ 2 + 27143 ^ 3) < 2 ^ 46 ∧
      16 * (3 ^ 3 + 27143 * 3) ^ 2 < 2 ^ 38 := by
  decide

/-- Item 7: the code heights. -/
theorem closed_comparisons_7 :
    max (max (max 6564 4640) 123720) 87483 < 2 ^ 17 ∧ 65536 * 1281 < 2 ^ 27 := by
  decide

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 9100 in
/-- The closed numerical comparisons of the size chapter, in one statement. -/
theorem closed_comparisons :
    (433 + 22 * 2 ^ 4608 < 2 ^ 4613 ∧ 4 + 1262628 + 16104 * 2 ^ 4608 < 2 ^ 4623 ∧
      1262628 = 433 * 2916 ∧ 16104 = 22 * 732) ∧
    2 + 10 * 2 ^ 4613 < 2 ^ 4617 ∧
    (10 ^ 12 < 2 ^ 40 ∧ 2250 + 2 ^ 9009 < 2 ^ 9010) ∧
    4096 * 85033 < 2 ^ 29 ∧
    ((96 * 10 ^ 13) ^ 13 < 2 ^ 650 ∧ 2210 * 116064000000 ^ 2 < 2 ^ 86) ∧
    (11243 + 2 * 7950 = 27143 ∧
      3 * 3 ^ 4 + 6 * 27143 * 3 ^ 2 + 27143 ^ 2 < 2 ^ 30 ∧
      2 * (3 ^ 6 + 5 * 27143 * 3 ^ 4 + 5 * 27143 ^ 2 * 3 ^ 2 + 27143 ^ 3) < 2 ^ 46 ∧
      16 * (3 ^ 3 + 27143 * 3) ^ 2 < 2 ^ 38) ∧
    (max (max (max 6564 4640) 123720) 87483 < 2 ^ 17 ∧ 65536 * 1281 < 2 ^ 27) :=
  ⟨closed_comparisons_1, closed_comparisons_2, closed_comparisons_3, closed_comparisons_4,
    closed_comparisons_5, closed_comparisons_6, closed_comparisons_7⟩

end ZInQ.Size
