import WeilTateLeftCountV001
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Enough roots of unity over an algebraically closed field of characteristic `0`

The roots-of-unity hypothesis of `WeilTate.left_nondeg_of_hom_finite_ker` for `k = k̄` of characteristic `0`
(e.g. `AlgebraicClosure K` for a number field `K`) and any finite commutative group.
-/

noncomputable section

namespace WeilTate

theorem hasEnoughRootsOfUnity_exponent (k G : Type*) [Field k] [IsAlgClosed k] [CharZero k]
    [CommGroup G] [Finite G] : HasEnoughRootsOfUnity k (Monoid.exponent G) := by
  haveI : NeZero ((Monoid.exponent G : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  infer_instance

end WeilTate

#check @WeilTate.hasEnoughRootsOfUnity_exponent
#print axioms WeilTate.hasEnoughRootsOfUnity_exponent
