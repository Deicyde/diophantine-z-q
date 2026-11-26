import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.FromOesterleAlone
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.OesterlePrintedComparison

/-! Fowler's order bound with the printed Oesterlé statement as its sole source premise. -/

namespace HDec.CMBranch.FowlerArithmetic

open NumberField TauCeti.GlobalNumberFields

universe u

/-- Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Astérisque
121–122 (1985), Exposé 631, Theorem 1 p. 310, with `C = 7000`. Here `d` is the positive
magnitude of the field discriminant and the product uses each prime divisor of `d` except
the largest. The class group is that of the full ring of integers.
Unread: §5.1, p. 321, takes the constant from [Ce] ("on montre (cf. [Ce]) que l'on peut
prendre C = 7000"); [Ce] has not been read. -/
def OesterleTheorem1Printed : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
    let d := (NumberField.discr K).natAbs
    (∏ p ∈ d.primeFactors.filter (fun p => ∃ q ∈ d.primeFactors, p < q),
      (1 - (⌊2 * Real.sqrt (p : ℝ)⌋ : ℝ) / ((p : ℝ) + 1))) * Real.log (d : ℝ) ≤
      7000 * (Nat.card (ClassGroup (𝓞 K)) : ℝ)

/-- The print is equivalent to the field-bound predicate on the exact domain of application. -/
theorem oesterleTheorem1Printed_iff_fieldBound :
    OesterleTheorem1Printed.{u} ↔
      ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
        Module.finrank ℚ K = 2 → OesterleFieldBound K := by
  have comparison (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
      (hK : Module.finrank ℚ K = 2) :
      OesterleFieldBound K ↔
        let d := (NumberField.discr K).natAbs
        (∏ p ∈ d.primeFactors.filter (fun p => ∃ q ∈ d.primeFactors, p < q),
          (1 - (⌊2 * Real.sqrt (p : ℝ)⌋ : ℝ) / ((p : ℝ) + 1))) * Real.log (d : ℝ) ≤
          7000 * (Nat.card (ClassGroup (𝓞 K)) : ℝ) := by
    obtain ⟨d, _, hd⟩ := exists_oesterle_discriminant K hK
    have hd' : d = (NumberField.discr K).natAbs := by omega
    subst d
    exact oesterleFieldBound_iff_printed K (RingOfIntegers.basis K) _
      (hd.trans (NumberField.discr_eq_discr K (RingOfIntegers.basis K)).symm)
  constructor
  · intro h K _ _ _ hK
    exact (comparison K hK).mpr (h K hK)
  · intro h K _ _ _ hK
    exact (comparison K hK).mp (h K hK)

/-- The only literature input to Fowler's bound is the printed effective estimate.
The remaining arguments specialize the conclusion to the given order and class-number bound. -/
theorem fowler_bound_of_oesterle_printed (h : OesterleTheorem1Printed.{u})
    {K : Type u} [Field K] [NumberField K] [IsTotallyComplex K]
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (n : ℕ) (hn : 0 < n) (hh : Nat.card (Pic O) ≤ n) :
    Real.sqrt |(O.discr : ℝ)| ≤ 2 * (n : ℝ)^2 * Real.exp (21000 * (n : ℝ)^2) :=
  fowler_bound_of_oesterle O hK ((oesterleTheorem1Printed_iff_fieldBound.mp h) K hK) n hn hh

end HDec.CMBranch.FowlerArithmetic
