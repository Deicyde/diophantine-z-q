/-
POSITIVE twin of the structural gate (must COMPILE). NEW fixture, 2026-11-14.

Same statement and same telescope as `neg/BadRangeMissing.lean`, with the range identification
`hjj` supplied. Its only role is to show that the rejection in the bad twin is caused by the
MISSING range identification and by nothing else in the telescope.

This is a STRUCTURAL applicability check. It asserts nothing about `jj` being trivial, about
`G_ℚ` being infinite, or about any universal falsity.
-/

import GaloisIndex

namespace ClimbGaloisIndexGate

open ClimbGaloisIndex

theorem range_gate_with_hjj {L : Type} [Field L] [CharZero L] [NumberField L]
    (ι : L →ₐ[ℚ] Qbar) (k : Type) [Field k] [CharZero k]
    {Γ : Type} [Group Γ] (jj : Γ →* GQ) (hjj : MonoidHom.range jj = fixSub ι) :
    (((MonoidHom.range jj).index : ℕ) : k) ≠ 0 :=
  cast_index_range_ne_zero_of_range_eq ι k jj hjj

#print axioms range_gate_with_hjj

end ClimbGaloisIndexGate
