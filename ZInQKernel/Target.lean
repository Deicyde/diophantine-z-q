import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Hyperoperation

/-!
# The target statement

`ZInQ.FrozenTarget` is the statement of upstream's quarantined theorem
`ZInQ.exists_bounded_integer_polynomial_defining_integers` in
`lean/Frozen/BoundedIntegerPolynomial.lean`, Theorem 1.1 of the 11/5 manuscript.
`scripts/check_target.py` checks that the two statements agree token for token.
-/

namespace ZInQ

/-- Theorem 1.1 of the 11/5 manuscript, exactly as frozen upstream. -/
def FrozenTarget : Prop :=
  ∃ P : MvPolynomial (Fin 292890231905) Int,
    P.totalDegree < hyperoperation 4 2 7 ∧
    (∀ m : Fin 292890231905 →₀ Nat,
      (P.coeff m).natAbs < hyperoperation 4 2 8) ∧
    ∀ q : Rat,
      (∃ w : Fin 292890231904 → Rat,
        MvPolynomial.eval₂ (Int.castRingHom Rat) (Fin.cons q w) P = 0) ↔
      ∃ z : Int, (z : Rat) = q

end ZInQ
