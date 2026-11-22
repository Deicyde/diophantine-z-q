/-
Adapted from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Original source: StacksFrontier/RingTheory/Derivation/MapPowChar.lean
Apache-2.0; upstream licence and source credits are preserved.
Compatibility: import paths remapped; metadata-only Stacks/SGA/EGA attributes omitted.
Mathematical declarations and proofs otherwise unchanged at initial port.
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations kill `p`-th powers in characteristic `p`

Over a ring of characteristic `p`, every derivation annihilates every `p`-th power.

## Main results

* `Derivation.map_pow_char_eq_zero`: a derivation of an algebra of characteristic `p` sends
  `x ^ p` to `0`.
-/

@[expose] public section

/-- In characteristic `p` a derivation kills `p`-th powers: `D (x ^ p) = 0`. -/

public lemma Derivation.map_pow_char_eq_zero {R A M : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module A M] [Module R M] (D : Derivation R A M) (p : ℕ)
    [CharP A p] (x : A) : D (x ^ p) = 0 := by
  rw [D.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

end
