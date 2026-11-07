import ZInQKernel.Size.Constants.Small
import ZInQKernel.Size.Constants.Closed

/-!
# Bounds for `D`

Blueprint: `size/constants/d-bounds.md`.

`2^(2^8008) < D < 2^(2^9010)` for `D = F · 3^(256 F⁴)`, `F = 324!`. The estimate is proved for a
variable `f` with `2^2000 < f < 2^2250`, by monotonicity of powers only, and then applied to
`F`; `D` is never evaluated.
-/

namespace ZInQ.Size

open Syntax AmbientPow

set_option exponentiation.threshold 9100 in
/-- The bounds for `D`, for a variable `f` with `2^2000 < f < 2^2250`. -/
theorem D_bounds_of {f : ℕ} (hf : 2 ^ 2000 < f ∧ f < 2 ^ 2250) :
    2 ^ 2 ^ 8008 < f * 3 ^ (256 * f ^ 4) ∧ f * 3 ^ (256 * f ^ 4) < 2 ^ 2 ^ 9010 := by
  have hf0 : 0 < f := (natPow_pos (by decide) _).trans hf.1
  constructor
  · have he : 2 ^ 8008 < 256 * f ^ 4 :=
      calc 2 ^ 8008 = 2 ^ 8 * (2 ^ 2000) ^ 4 := by
            rw [← natPow_mul, ← natPow_add]
        _ < 2 ^ 8 * f ^ 4 :=
            Nat.mul_lt_mul_of_pos_left (natPow_lt_natPow_left hf.1 (by decide)) (by decide)
    calc 2 ^ 2 ^ 8008 < 2 ^ (256 * f ^ 4) := natPow_lt_natPow_right (by decide) he
      _ ≤ 3 ^ (256 * f ^ 4) := natPow_le_natPow_left (by decide) _
      _ ≤ f * 3 ^ (256 * f ^ 4) := Nat.le_mul_of_pos_left _ hf0
  · have he : 2 * (256 * f ^ 4) < 2 ^ 9009 :=
      calc 2 * (256 * f ^ 4) < 2 * (256 * (2 ^ 2250) ^ 4) :=
            Nat.mul_lt_mul_of_pos_left
              (Nat.mul_lt_mul_of_pos_left (natPow_lt_natPow_left hf.2 (by decide)) (by decide))
              (by decide)
        _ = 2 ^ 9009 := by rw [← natPow_mul]; norm_num
    have hp : 3 ^ (256 * f ^ 4) < 2 ^ 2 ^ 9009 :=
      calc 3 ^ (256 * f ^ 4) < (2 ^ 2) ^ (256 * f ^ 4) :=
            natPow_lt_natPow_left (by decide) (Nat.mul_ne_zero (by decide) (pow_ne_zero _ hf0.ne'))
        _ = 2 ^ (2 * (256 * f ^ 4)) := (natPow_mul _ _ _).symm
        _ < 2 ^ 2 ^ 9009 := natPow_lt_natPow_right (by decide) he
    calc f * 3 ^ (256 * f ^ 4) < 2 ^ 2250 * 2 ^ 2 ^ 9009 := Nat.mul_lt_mul_of_lt_of_lt hf.2 hp
      _ = 2 ^ (2250 + 2 ^ 9009) := (natPow_add _ _ _).symm
      _ < 2 ^ 2 ^ 9010 := natPow_lt_natPow_right (by decide) closed_comparisons_3.2

/-- `2^(2^8008) < D < 2^(2^9010)`. -/
theorem D_bounds : 2 ^ 2 ^ 8008 < D ∧ D < 2 ^ 2 ^ 9010 := by
  rw [D_eq]; exact D_bounds_of F_bounds

theorem D_gt : 2 ^ 2 ^ 8008 < D := D_bounds.1

theorem D_lt : D < 2 ^ 2 ^ 9010 := D_bounds.2

set_option exponentiation.threshold 9100 in
/-- `2^(2^k) < D` for `k ≤ 8008`. -/
theorem two_pow_two_pow_lt_D {k : ℕ} (hk : k ≤ 8008) : 2 ^ 2 ^ k < D :=
  (natPow_le_natPow_right (by decide) (natPow_le_natPow_right (by decide) hk)).trans_lt D_gt

/-- Every number below `2^8008` is below `2^(2^8008)`, hence below `D`. -/
theorem lt_D_of_lt {n : ℕ} (hn : n < 2 ^ 8008) : n < D :=
  calc n < 2 ^ n := lt_two_natPow n
    _ < 2 ^ 2 ^ 8008 := natPow_lt_natPow_right (by decide) hn
    _ < D := D_gt

end ZInQ.Size
