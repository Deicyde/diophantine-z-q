import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionFourierComparison
import Mathlib.Algebra.Field.ZMod

/-!
# Prime additive characters in the torsion pairing convention

The additive character is the actual torsion root exponential, evaluated on
canonical residue lifts. Its kernel and finite sum are proved from the actual
primitive root and the finite geometric sum.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

/-- The actual positive exponential on a prime residue. -/
def phase (p : ℕ) (x : ZMod p) : ℂ := Torsion.w p (x.val : ℤ)

lemma w_shift (p : ℕ) [NeZero p] (a k : ℤ) :
    Torsion.w p (a + (p : ℤ) * k) = Torsion.w p a := by
  have h := TorsionFourierComparison.character_shift p 0 1 a 0 k 0
  simpa only [TorsionFourierComparison.character, Int.cast_zero, Int.cast_one,
    one_mul, zero_mul, sub_zero, mul_zero, add_zero,
    AllLevelTorsionCoefficients.w_eq_exp] using h

/-- Representative independence, with no unguarded signed-to-natural conversion. -/
theorem phase_intCast (p : ℕ) [NeZero p] (a : ℤ) :
    phase p (a : ZMod p) = Torsion.w p a := by
  have he : a = (a : ZMod p).val + (p : ℤ) * (a / (p : ℤ)) := by
    rw [ZMod.val_intCast]
    exact (Int.emod_add_mul_ediv a (p : ℤ)).symm
  change Torsion.w p ((a : ZMod p).val : ℤ) = Torsion.w p a
  have hs := w_shift p ((a : ZMod p).val : ℤ) (a / (p : ℤ))
  rw [← he] at hs
  exact hs.symm

lemma w_add (p : ℕ) [NeZero p] (a b : ℤ) :
    Torsion.w p (a + b) = Torsion.w p a * Torsion.w p b := by
  rw [AllLevelTorsionCoefficients.w_eq_exp, AllLevelTorsionCoefficients.w_eq_exp,
    AllLevelTorsionCoefficients.w_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The actual phase is additive-to-multiplicative. -/
theorem phase_add (p : ℕ) [NeZero p] (x y : ZMod p) :
    phase p (x + y) = phase p x * phase p y := by
  have hx : ((x.val : ℤ) : ZMod p) = x := by simp
  have hy : ((y.val : ℤ) : ZMod p) = y := by simp
  rw [← hx, ← hy, ← Int.cast_add, phase_intCast, w_add, phase_intCast, phase_intCast]

@[simp] theorem phase_zero (p : ℕ) : phase p 0 = 1 := by simp [phase, Torsion.w]

lemma finite_residue_val (p : ℕ) [NeZero p] (t : Fin p) : (ZMod.finEquiv p t).val = t.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- The actual phase is one only on the zero residue. -/
theorem phase_eq_one_iff (p : ℕ) [NeZero p] (x : ZMod p) : phase p x = 1 ↔ x = 0 := by
  rw [phase, AllLevelTorsionCoefficients.w_eq_one_iff]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp

/-- The complete prime phase sum is zero. -/
theorem sum_phase (p : ℕ) [Fact p.Prime] : (∑ x : ZMod p, phase p x) = 0 := by
  have hp := (Fact.out : p.Prime)
  let : NeZero p := ⟨hp.ne_zero⟩
  have he : (∑ x : ZMod p, phase p x) = ∑ t : Fin p, (Torsion.zeta p) ^ t.val := by
    rw [← (ZMod.finEquiv p).toEquiv.sum_comp]
    apply Finset.sum_congr rfl
    intro t _
    change Torsion.w p ((ZMod.finEquiv p t).val : ℤ) = Torsion.zeta p ^ t.val
    rw [finite_residue_val]
    simp only [Torsion.w, zpow_natCast]
  have hζ : Torsion.zeta p ≠ 1 := by
    have hn : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast hp.not_dvd_one
    have h := (AllLevelTorsionCoefficients.w_eq_one_iff p 1).not.mpr hn
    simpa [Torsion.w] using h
  rw [he, TorsionFourierComparison.finite_geometric p (Torsion.zeta p)
    (AllLevelTorsionCoefficients.complex_root_primitive p).pow_eq_one, if_neg hζ]

/-- Orthogonality for each actual prime additive character. -/
theorem sum_phase_mul (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    (∑ x : ZMod p, phase p (a * x)) = if a = 0 then (p : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [if_neg ha]
    let e : ZMod p ≃ ZMod p := Equiv.mulLeft₀ a ha
    have hsum := e.sum_comp (phase p)
    change (∑ x : ZMod p, phase p (a * x)) = ∑ x : ZMod p, phase p x at hsum
    rw [hsum, sum_phase p]

/-- The scalar phase has the literal positive exponential orientation. -/
theorem phase_eq_exp (p : ℕ) [NeZero p] (a : ℤ) :
    phase p (a : ZMod p) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (p : ℂ)) := by
  rw [phase_intCast, AllLevelTorsionCoefficients.w_eq_exp]

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
