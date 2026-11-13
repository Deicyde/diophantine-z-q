import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod

set_option linter.style.haveILetI false
example {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V] [Finite V] (r : ℕ) (hc : Nat.card V = ℓ ^ r) :
    True := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  haveI hfin : Module.Finite (ZMod ℓ) V := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := V)
  have hfr : Module.finrank (ZMod ℓ) V = r := by
    rw [hc, Nat.card_zmod] at h1
    exact (Nat.pow_right_injective hℓ.out.two_le h1).symm
  let b : Module.Basis (Fin r) (ZMod ℓ) V := Module.finBasisOfFinrankEq (ZMod ℓ) V hfr
  have := b 0
  trivial
