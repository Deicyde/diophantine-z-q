import ZInQKernel.Size.Constants.Catalogue
import ZInQKernel.Size.FormalMultiple.Existence

/-!
# Size of the formal multiple constant

Blueprint: `size/constants/formal-multiple-size.md`.

The existence of a successful formal multiple (`size/formal-multiple/formal-multiple-existence.md`,
`ZInQ.Size.exists_formal_multiple` and `ZInQ.Size.M0_bounds`) gives `1 ≤ M₀ ≤ N_s^10`, using
only `N_s ≥ 1` (`Syntax.Ns_pos`, from Dirichlet's theorem); with `N_s < 2^(2^4613)` this gives
`c_* = 4 M₀ < 2^(2^4617)`.
-/

namespace ZInQ.Size

open Syntax AmbientPow

set_option exponentiation.threshold 4700 in
/-- The estimate for `c_*`, for variables. -/
theorem four_mul_lt_of {m n : ℕ} (hm : m ≤ n ^ 10) (hn : n < 2 ^ 2 ^ 4613) :
    4 * m < 2 ^ 2 ^ 4617 := by
  have he : 2 + 2 ^ 4613 * 10 < 2 ^ 4617 := by
    rw [Nat.mul_comm]; exact closed_comparisons_2
  calc 4 * m ≤ 4 * n ^ 10 := Nat.mul_le_mul_left 4 hm
    _ < 4 * (2 ^ 2 ^ 4613) ^ 10 :=
        Nat.mul_lt_mul_of_pos_left (natPow_lt_natPow_left hn (by decide)) (by decide)
    _ = 2 ^ 2 * (2 ^ 2 ^ 4613) ^ 10 :=
        congrArg (· * (2 ^ 2 ^ 4613) ^ 10) (by norm_num : (4 : ℕ) = 2 ^ 2)
    _ = 2 ^ 2 * 2 ^ (2 ^ 4613 * 10) := by rw [← natPow_mul]
    _ = 2 ^ (2 + 2 ^ 4613 * 10) := (natPow_add _ _ _).symm
    _ < 2 ^ 2 ^ 4617 := natPow_lt_natPow_right (by decide) he

/-- `c_* < 2^(2^4617)`. -/
theorem cstar_lt (hCAT : CatalogueBound8) : cstar < 2 ^ 2 ^ 4617 := by
  rw [cstar_eq]; exact four_mul_lt_of (M0_bounds Ns_pos).2.1 (Ns_bounds hCAT).2

/-- Size of the formal multiple constant (the blueprint statement). -/
theorem formal_multiple_size (hCAT : CatalogueBound8) :
    1 ≤ M0 ∧ M0 ≤ Ns ^ 10 ∧ cstar < 2 ^ 2 ^ 4617 :=
  ⟨(M0_bounds Ns_pos).1, (M0_bounds Ns_pos).2.1, cstar_lt hCAT⟩

end ZInQ.Size
