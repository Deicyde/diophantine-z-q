import ZInQKernel.Contrib.HilbertDifferent.GlobalFormula

/-!
# Exact GLOBAL T20 statement and endpoint checks

The expected proposition below is independently spelled from the frozen main
`GlueConductor.HilbertDifferentFormula`. It retains every original field,
Galois, prime and nonzero-prime quantifier, and no extra localization, generator,
comparison, literature-leaf or `Fact` premise. The tests consume the new full
global proof, rather than reusing the older monogenic special case.
-/

open NumberField Finset
open scoped Pointwise HilbertDifferentLocalization

namespace ZInQ.Contrib.HilbertDifferent.GlobalFormulaChecks

/-- Independent spelling of the original GLOBAL target, with no universe parameters. -/
def expectedGlobalHilbert : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (GlueConductor.ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (GlueConductor.ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- The independent statement has the same actual body as the main proposition. -/
theorem statement_agrees : expectedGlobalHilbert ↔ GlueConductor.HilbertDifferentFormula := Iff.rfl

/-- The full closed independently spelled GLOBAL type, with no added binder. -/
theorem exact_closed_global_shape : expectedGlobalHilbert := hilbertDifferentFormula

/-- The exact exponent is unchanged when a different eventual-triviality cutoff is chosen.
In particular the result is not dependent on a preferred positive cutoff. -/
theorem exact_at_any_triviality_witness (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) (n : ℕ)
    (hn : GlueConductor.ramGroup L P n = ⊥) :
    P ^ (ramificationSum L P n) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (ramificationSum L P n + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  obtain ⟨m, hm, hdiv, hnext⟩ := hilbertDifferentAt_localization L P hP
  have hsum : ramificationSum L P m = ramificationSum L P n :=
    (finsum_ramCard_sub_one_eq_sum L P hm).symm.trans
      (finsum_ramCard_sub_one_eq_sum L P hn)
  simpa only [hsum] using And.intro hdiv hnext

/-- A zero cutoff gives the genuine successor test `¬P ∣ differentIdeal`, not a vacuous
zero-power divisibility claim. It is derived from the full global proof. -/
theorem zero_cutoff_not_dvd (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (hzero : GlueConductor.ramGroup L P 0 = ⊥) : ¬ P ∣ differentIdeal ℤ (𝓞 L) := by
  simpa [ramificationSum] using (exact_at_any_triviality_witness L P hP 0 hzero).2

/-- All nonzero primes of the trivial global extension satisfy the exact formula at `n=0`.
This uses the new full target, not an assumed monogenicity premise. -/
theorem rational_zero_witness (P : Ideal (𝓞 ℚ)) [P.IsPrime] (hP : P ≠ ⊥) :
    GlueConductor.ramGroup ℚ P 0 = ⊥ ∧
      P ^ (∑ i ∈ range 0, (GlueConductor.ramCard ℚ P i - 1)) ∣ differentIdeal ℤ (𝓞 ℚ) ∧
      ¬ P ^ (∑ i ∈ range 0, (GlueConductor.ramCard ℚ P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 ℚ) := by
  have hzero : GlueConductor.ramGroup ℚ P 0 = ⊥ := Subsingleton.elim _ _
  exact ⟨hzero, exact_at_any_triviality_witness ℚ P hP 0 hzero⟩

/-- Zero-exponent contraction is included in the actual localization power comparison. -/
theorem zero_power_localization (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ 0).comap
      (algebraMap (𝓞 L) (Localization.AtPrime P)) = P ^ 0 := by
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  exact primeLocalization_comap_maximalIdeal_pow P 0

end ZInQ.Contrib.HilbertDifferent.GlobalFormulaChecks

#check @ZInQ.Contrib.HilbertDifferent.hilbertDifferentFormula
#check @ZInQ.Contrib.HilbertDifferent.localizationDecompositionEquiv
#check @ZInQ.Contrib.HilbertDifferent.localizationDecompositionEquiv_algebraMap
#check @ZInQ.Contrib.HilbertDifferent.ramCard_eq_card_localization
#print axioms ZInQ.Contrib.HilbertDifferent.primeLocalization_comap_maximalIdeal_pow
#print axioms ZInQ.Contrib.HilbertDifferent.primeLocalization_surjective_mod_pow
#print axioms ZInQ.Contrib.HilbertDifferent.LocalizationModel.local_integralClosure
#print axioms ZInQ.Contrib.HilbertDifferent.LocalizationModel.base_residue_perfect
#print axioms ZInQ.Contrib.HilbertDifferent.localizationDecompositionEquiv
#print axioms ZInQ.Contrib.HilbertDifferent.localizationDecompositionEquiv_algebraMap
#print axioms ZInQ.Contrib.HilbertDifferent.ramGroup_localization_comap
#print axioms ZInQ.Contrib.HilbertDifferent.ramCard_eq_card_localization
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_localization
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentFormula
#print axioms ZInQ.Contrib.HilbertDifferent.GlobalFormulaChecks.exact_closed_global_shape
#print axioms ZInQ.Contrib.HilbertDifferent.GlobalFormulaChecks.rational_zero_witness
