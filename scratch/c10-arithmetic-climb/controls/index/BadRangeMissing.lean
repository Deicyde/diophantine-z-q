/-
STRUCTURAL GATE, must be REJECTED. NEW fixture, 2026-11-14.

Applies the actual `ClimbGaloisIndex.cast_index_range_ne_zero_of_range_eq` with the full given
telescope — `L`, `ι`, `k`, `jj` — but WITHOUT the range identification `hjj`.

Intended rejection: the applied term still carries the hypothesis
`MonoidHom.range jj = fixSub ι`, so its type does not match the claimed conclusion. That is a
STRUCTURAL inapplicability gate: without a verified range identification the index fact cannot be
transported to `range jj`. It is NOT a parse or import error, NOT a claim that `jj` is trivial or
that `G_ℚ` is infinite, and NOT a universal falsity claim. The positive twin
`neg/RangeGatePositive.lean` compiles with the identical telescope plus `hjj`.
-/

import GaloisIndex

namespace ClimbGaloisIndexGateBad

open ClimbGaloisIndex

theorem range_gate_without_hjj {L : Type} [Field L] [CharZero L] [NumberField L]
    (ι : L →ₐ[ℚ] Qbar) (k : Type) [Field k] [CharZero k]
    {Γ : Type} [Group Γ] (jj : Γ →* GQ) :
    (((MonoidHom.range jj).index : ℕ) : k) ≠ 0 :=
  cast_index_range_ne_zero_of_range_eq ι k jj

end ClimbGaloisIndexGateBad
