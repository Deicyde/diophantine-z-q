import ZInQ.BitwiseMacros

/-!
# The bitwise AND gadget

Blueprint: `compiler/natural/exponential/bit-and.md`.

`z = x AND y` iff `x = z + a` and `y = z + b` for some `a, b` with `z, a, b` pairwise
bit-disjoint. Upstream's `ZInQ.NaturalBitwiseMacros.bit_and_iff_land_eq` proves the same with
each disjointness written as the orthogonality macro; we unfold the macros with
`orthogonal_iff_land_eq_zero`.
-/

namespace ZInQ

/-- The bitwise AND gadget, with disjointness written bitwise. -/
theorem bitAnd_gadget_iff (z x y : ℕ) :
    (∃ a b : ℕ, x = z + a ∧ y = z + b ∧ z &&& a = 0 ∧ z &&& b = 0 ∧ a &&& b = 0) ↔
      z = x &&& y := by
  rw [show z = x &&& y ↔ z = Nat.land x y from Iff.rfl,
    ← NaturalBitwiseMacros.bit_and_iff_land_eq, NaturalBitwiseMacros.bit_and]
  simp only [NaturalBitwiseMacros.orthogonal_iff_land_eq_zero]
  rfl

/-- The same gadget with each disjointness condition written as the compiler's orthogonality
macro (`C(p + q, p)` odd). -/
theorem bitAnd_macro_iff (z x y : ℕ) :
    NaturalBitwiseMacros.bit_and z x y ↔ z = x &&& y :=
  NaturalBitwiseMacros.bit_and_iff_land_eq z x y

end ZInQ
