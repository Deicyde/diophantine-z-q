import Mathlib
import ZInQKernel.Contrib.Different.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild

/-!
# The global Serre bound T21 via Tau Ceti's wild different bound

* `ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound` (T21,
  `v_P(𝔇_{𝓞 L/ℤ}) ≤ e - 1 + e · v_p(e)`), from Tau Ceti's
  `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span`
  (`LocalGlobal/Different/Wild.lean`, Serre's bound transported from the completion) and the
  bridge lemmas of `Bridge.lean`;
* `ZInQ.Contrib.Different.D1_genuine_closed`: `GlueConductor.D1_genuine` with both leaves
  discharged.

T20 (`hilbertDifferentFormula`) is in `Bridge.lean`. A second proof of T21, from task
t-different's local bound `PkgI6.differentBound` instead of Tau Ceti's `Wild.lean`, is
`SerreLocal.lean`. No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.Different

/-- **T21, global (`GlueConductor.SerreDifferentBound`).** -/
theorem serreDifferentBound : GlueConductor.SerreDifferentBound := by
  intro L _ _ p hp P _ hPl
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set w := toHeightOneSpectrum P hP0 with hw
  set v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hv
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hW := HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span
    v w
  have hwP : w.asIdeal = P := rfl
  rw [hwP, ← ramificationIdx_int_eq, ← differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat]
    at hW
  have hS := multiplicity_span_ramificationIdx_le p hp P hP0
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have hF : FiniteMultiplicity P (differentIdeal ℤ (𝓞 L)) :=
    Ideal.finiteMultiplicity hPtop differentIdeal_ne_bot
  apply hF.not_pow_dvd_of_multiplicity_lt
  omega

/-- **`GlueConductor.D1_genuine` with both leaves discharged.** For a Galois number field `L`, a
prime `P | p` with ramification index `e ≤ a!` and a lower index `b` with `G_b ≠ 1`, the upper
index `φ(b)` is at most `4a²`. -/
theorem D1_genuine_closed (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ)
    [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : GlueConductor.ramGroup L P b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2 :=
  GlueConductor.D1_genuine hilbertDifferentFormula serreDifferentBound L p P a ha hea b hb

end ZInQ.Contrib.Different
