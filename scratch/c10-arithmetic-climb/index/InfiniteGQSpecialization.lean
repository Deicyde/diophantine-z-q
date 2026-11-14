/-
climb/infinite-gq — concrete ascription of the universal trivial-`jj` control (NEW file).

`ClimbInfiniteGQ.trivial_jj_cast_zero` is already universal in the group `Γ` and the field `k`,
and `(1 : Γ →* G_ℚ)` is already an actual monoid homomorphism. This file adds nothing
mathematical: it only ascribes that universal object at the concrete `Γ = Unit`, `k = ℚ`, so the
control is visible as a closed statement about named objects. No Eisenstein, no θ/j source, no
new fiction.
-/

import InfiniteGQ

namespace ClimbInfiniteGQSpec

open ClimbInfiniteGQ ClimbGaloisIndex

/-- The trivial homomorphism from `Unit` into `G_ℚ` has range `⊥` and index `0`. -/
theorem unit_range_bot_index_zero :
    MonoidHom.range (1 : Unit →* GQ) = ⊥ ∧ (MonoidHom.range (1 : Unit →* GQ)).index = 0 :=
  trivial_jj_index_zero

/-- …so over `ℚ` its index casts to `0`: a concrete `jj` for which `hidx` is unobtainable. -/
theorem unit_rat_cast_zero :
    (((MonoidHom.range (1 : Unit →* GQ)).index : ℕ) : ℚ) = 0 :=
  trivial_jj_cast_zero ℚ

#check @unit_range_bot_index_zero
#check @unit_rat_cast_zero
#print axioms unit_range_bot_index_zero
#print axioms unit_rat_cast_zero

end ClimbInfiniteGQSpec
