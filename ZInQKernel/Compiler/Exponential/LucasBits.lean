import ZInQ.BitwiseMacros

/-!
# Lucas's criterion for bit inclusion and disjointness

Blueprint: `compiler/natural/exponential/lucas-bits.md`.

`C(b, a)` is odd iff `a AND b = a`, and `C(a + b, a)` is odd iff `a AND b = 0` (upstream
`ZInQ.NaturalBitwiseMacros.choose_odd_iff_land_eq` and `choose_add_odd_iff_land_eq_zero`, from
Mathlib's Lucas theorem `Choose.choose_modEq_choose_mod_mul_choose_div_nat`).
-/

namespace ZInQ

/-- Lucas's criterion: `C(b, a)` is odd iff `a` is masked by `b`. -/
theorem lucas_choose_odd_iff_masked (a b : ℕ) : Odd (Nat.choose b a) ↔ a &&& b = a :=
  NaturalBitwiseMacros.choose_odd_iff_land_eq a b

/-- `C(a + b, a)` is odd iff `a` and `b` have disjoint bits. -/
theorem lucas_choose_add_odd_iff_disjoint (a b : ℕ) :
    Odd (Nat.choose (a + b) a) ↔ a &&& b = 0 :=
  NaturalBitwiseMacros.choose_add_odd_iff_land_eq_zero a b

end ZInQ
