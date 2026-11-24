import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic

/-!
# Integral congruence powers

The power estimate uses only the linear term and a quadratic remainder.
It includes the prime two at principal depth one; no torsion-free claim
about the first two-adic congruence subgroup is made.
-/

noncomputable section
set_option autoImplicit false

namespace IntegralCongruence

variable {R : Type*} [Ring R]

/-- The binomial expansion to first order, valid in a noncommutative ring. -/
theorem power_quadratic_remainder (x : R) (m : ℕ) :
    ∃ y : R, (1 + x) ^ m = 1 + (m : R) * x + x ^ 2 * y := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨(m : R) + y + y * x, ?_⟩
    rw [pow_succ, hy, Nat.cast_succ]
    have hc : (m : R) * x ^ 2 = x ^ 2 * (m : R) := (Nat.cast_commute m (x ^ 2)).eq
    calc
      (1 + (m : R) * x + x ^ 2 * y) * (1 + x) =
          1 + (m : R) * x + x ^ 2 * y + x + (m : R) * x ^ 2 + x ^ 2 * (y * x) := by
        noncomm_ring
      _ = 1 + ((m : R) + 1) * x + x ^ 2 * ((m : R) + y + y * x) := by
        rw [hc]
        noncomm_ring

/-- Raising a principal congruence element to the residue characteristic
increases its depth by at least one, including characteristic two. -/
theorem power_increases_depth (ell k : ℕ) (hk : 1 ≤ k) (B : R) :
    ∃ C : R, (1 + (ell : R) ^ k * B) ^ ell = 1 + (ell : R) ^ (k + 1) * C := by
  obtain ⟨Y, hY⟩ := power_quadratic_remainder ((ell : R) ^ k * B) ell
  refine ⟨B + (ell : R) ^ (k - 1) * B ^ 2 * Y, ?_⟩
  rw [hY, ((Nat.cast_commute ell B).pow_left k).mul_pow]
  have he : k * 2 = (k + 1) + (k - 1) := by omega
  rw [← pow_mul, he, pow_add]
  rw [← mul_assoc (ell : R) ((ell : R) ^ k) B, ← pow_succ']
  noncomm_ring

/-- A uniform power bound at every finite congruence level. -/
theorem iterated_depth (ell : ℕ) (B : R) (n : ℕ) :
    ∃ C : R, (1 + (ell : R) * B) ^ (ell ^ n) = 1 + (ell : R) ^ (n + 1) * C := by
  induction n with
  | zero => exact ⟨B, by simp⟩
  | succ n ih =>
    obtain ⟨C, hC⟩ := ih
    rw [pow_succ, pow_mul, hC]
    simpa only [Nat.succ_eq_add_one] using power_increases_depth ell (n + 1) (by omega) C

/-- Principal congruence units in a ring killed by a power of ell have
ell-power order. This is not a finite-image assumption. -/
theorem principal_unit_power (ell n : ℕ) (hn : (ell : R) ^ (n + 1) = 0)
    (g : Rˣ) (B : R) (hg : (g : R) = 1 + (ell : R) * B) : g ^ (ell ^ n) = 1 := by
  apply Units.ext
  change (g : R) ^ (ell ^ n) = 1
  rw [hg]
  obtain ⟨C, hC⟩ := iterated_depth ell B n
  simpa [hn] using hC

#print axioms power_quadratic_remainder
#print axioms power_increases_depth
#print axioms iterated_depth
#print axioms principal_unit_power

end IntegralCongruence
