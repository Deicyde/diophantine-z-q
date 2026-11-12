import Mathlib
/-! Non-vacuity check: the hypothesis classes of the local leaves of `I6.lean` hold for `ℤ_[p]`
(the trivial extension `ℤ_[p] → ℤ_[p]`), so those leaves are not vacuous for lack of models. -/
open IsLocalRing
variable (p : ℕ) [Fact p.Prime]
example : IsDiscreteValuationRing ℤ_[p] := inferInstance
example : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] := inferInstance
example : PerfectField (ResidueField ℤ_[p]) := inferInstance
example : Finite (ResidueField ℤ_[p]) := inferInstance
example : Module.Finite ℤ_[p] ℤ_[p] := inferInstance
example : Module.IsTorsionFree ℤ_[p] ℤ_[p] := inferInstance
attribute [local instance] FractionRing.liftAlgebra in
example : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing ℤ_[p]) := inferInstance
