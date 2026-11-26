import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrder
import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.UniversalShort
import Mathlib.Data.Nat.Totient

/-! # The detector's local base and its tame levels -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion

private theorem localNat_isUnit (ell : ℕ) [Fact ell.Prime] {m : ℕ} (hm : ¬ ell ∣ m) :
    IsUnit (m : LocalIntegers ell) := by
  have hmem : (m : ℤ) ∈ (integerPrimeIdeal ell).primeCompl := by
    change (m : ℤ) ∉ Ideal.span {(ell : ℤ)}
    simpa [Ideal.mem_span_singleton, Int.natCast_dvd] using hm
  simpa using IsLocalization.map_units (LocalIntegers ell) ⟨(m : ℤ), hmem⟩

/-- The prime exclusion in tex 8366–8368 permits excluding 3 and the prime
divisors of the fixed `N * φ(N)`. Under the explicit exclusions, 6, the
level, and the order of its unit group are units in the detector's local ring. -/
theorem detector_units (ell N : ℕ) [Fact ell.Prime] [NeZero N] (_h5 : 5 ≤ ell)
    (h : ¬ ell ∣ N * N.totient) :
    IsUnit (6 : LocalIntegers ell) ∧ IsUnit (N : LocalIntegers ell) ∧
      IsUnit (Nat.card ((ZMod N)ˣ) : LocalIntegers ell) := by
  classical
  have hp : ell.Prime := Fact.out
  have h6 : ¬ ell ∣ 6 := by
    intro hd
    have h₂₃ := (hp.dvd_mul.mp (show ell ∣ 2 * 3 from hd))
    exact h₂₃.elim (fun h₂ => by have := Nat.le_of_dvd (by decide : 0 < 2) h₂; omega)
      (fun h₃ => by have := Nat.le_of_dvd (by decide : 0 < 3) h₃; omega)
  have hN : ¬ ell ∣ N := fun hd => h (dvd_mul_of_dvd_left hd _)
  have hφ : ¬ ell ∣ N.totient := fun hd => h (dvd_mul_of_dvd_right hd _)
  refine ⟨localNat_isUnit ell h6, localNat_isUnit ell hN, ?_⟩
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  exact localNat_isUnit ell hφ

/-- The universal exact-order cover of the short Weierstrass locus over
`ℤ_(ell)`. The explicit exclusions use tex 8366–8368, where the detector
choice permits any fixed finite set of bad primes. -/
noncomputable abbrev UniversalExactOrderAlgebra (ell N : ℕ) [Fact ell.Prime] [NeZero N]
    (h5 : 5 ≤ ell) (h : ¬ ell ∣ N * N.totient) :=
  ExactOrderAlgebra (shortFamily (LocalIntegers ell))
    (show IsUnit (N : ShortBase (LocalIntegers ell)) by
      exact_mod_cast (detector_units ell N h5 h).2.1.map
        (algebraMap (LocalIntegers ell) (ShortBase (LocalIntegers ell))))

/-- The universal cover is a finite étale algebra over the short locus with
the explicit detector exclusions from tex 8366–8368. -/
theorem universalExactOrder_finite_etale (ell N : ℕ) [Fact ell.Prime] [NeZero N]
    (h5 : 5 ≤ ell) (h : ¬ ell ∣ N * N.totient) :
    Module.Finite (ShortBase (LocalIntegers ell)) (UniversalExactOrderAlgebra ell N h5 h) ∧
      Algebra.Etale (ShortBase (LocalIntegers ell)) (UniversalExactOrderAlgebra ell N h5 h) :=
  exactOrderAlgebra_finite_etale _ _

#print axioms localNat_isUnit
#print axioms detector_units
#print axioms universalExactOrder_finite_etale

end WeierstrassCurve.ModelLevels
