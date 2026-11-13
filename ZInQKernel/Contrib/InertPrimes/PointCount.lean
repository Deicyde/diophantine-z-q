import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Affine point counts at primes congruent to three modulo four

If `-1` is not a square in a finite field and `f (-x) = -f x`, negation
pairs the terms of the quadratic-character sum with their negatives.
The square-root fiber formula then gives exactly one affine point per
field element on average. Applying this to `f x = x^3 - d^2*x` requires
no nonvanishing hypothesis on `d`; in particular, it also counts the
singular fibers. The application to nonsingular projective points is
separate from this module.
-/

namespace ZInQ.Contrib.InertPrimes

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An odd function has zero quadratic-character sum when `-1` is a nonsquare. -/
theorem quadraticChar_sum_comp_of_odd (f : F → F) (hf : ∀ x, f (-x) = -f x)
    (hminus : ¬ IsSquare (-1 : F)) : ∑ x : F, quadraticChar F (f x) = 0 := by
  have hχ : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr hminus
  have hodd (x : F) : quadraticChar F (f (-x)) = -quadraticChar F (f x) := by
    rw [hf x, neg_eq_neg_one_mul, map_mul, hχ, neg_one_mul]
  have hsum := Equiv.sum_comp (Equiv.neg F) (fun x => quadraticChar F (f x))
  simp only [Equiv.neg_apply, hodd, Finset.sum_neg_distrib] at hsum
  omega

/-- The affine equation `y² = f x` has `#F` solutions for odd `f` if `-1` is a nonsquare. -/
theorem natCard_affine_of_odd (f : F → F) (hf : ∀ x, f (-x) = -f x)
    (hminus : ¬ IsSquare (-1 : F)) :
    Nat.card {xy : F × F // xy.2 ^ 2 = f xy.1} = Fintype.card F := by
  classical
  have hF : ringChar F ≠ 2 := fun h =>
    hminus (FiniteField.isSquare_of_char_two h (-1 : F))
  apply Int.natCast_inj.mp
  calc
    (Nat.card {xy : F × F // xy.2 ^ 2 = f xy.1} : ℤ) =
        ∑ x : F, (Fintype.card {y : F // y ^ 2 = f x} : ℤ) := by
      rw [Nat.card_eq_fintype_card,
        Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun x y : F => y ^ 2 = f x)),
        Fintype.card_sigma, Nat.cast_sum]
    _ = ∑ x : F, (quadraticChar F (f x) + 1) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Set.toFinset_ofPred, Fintype.card_subtype] using
        quadraticChar_card_sqrts hF (f x)
    _ = (Fintype.card F : ℤ) := by
      rw [Finset.sum_add_distrib, quadraticChar_sum_comp_of_odd f hf hminus]
      simp

end FiniteField

/-- For every `d`, the affine congruent-number equation has exactly `p` solutions
at a prime `p ≡ 3 (mod 4)`. This includes `d = 0` and `p ∣ d`. -/
theorem natCard_affine_cd_of_mod_four (p d : ℕ) [Fact p.Prime] (hp : p % 4 = 3) :
    Nat.card {xy : ZMod p × ZMod p //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} = p := by
  have hminus : ¬ IsSquare (-1 : ZMod p) := by
    rw [FiniteField.isSquare_neg_one_iff, ZMod.card, hp]
    simp
  simpa only [ZMod.card] using
    natCard_affine_of_odd (fun x : ZMod p => x ^ 3 - (d : ZMod p) ^ 2 * x)
      (fun x => by ring) hminus

end ZInQ.Contrib.InertPrimes
