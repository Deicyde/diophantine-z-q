import ZInQKernel.Contrib.HilbertDifferent.Monogenic
import ZInQKernel.Contrib.HilbertDifferent.Transport
import ZInQKernel.Contrib.HilbertDifferent.IntegralClosure

/-!
# T20 partial-result shape and endpoint checks

These are kernel-checked checks of the proved partial, not a provider for the
closed global target. They explicitly cover prime-power exponent zero, the
trivial Galois group over ℚ, the excluded zero prime's filtration, and changing
an eventual-triviality truncation. No test imports the draft statement extraction.
-/

open NumberField Finset

namespace ZInQ.Contrib.HilbertDifferent.Checks

/-- Independently spelled main conclusion, with the genuinely needed extra monogenic hypothesis.
All global nonzero primes are quantified; no tame-only or residue-characteristic restriction. -/
theorem exact_global_shape_with_generator :
    ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      ∀ (x : 𝓞 L), Algebra.adjoin ℤ {x} = ⊤ →
        ∀ (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
          ∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
            P ^ (∑ i ∈ range n, (GlueConductor.ramCard L P i - 1)) ∣
              differentIdeal ℤ (𝓞 L) ∧
            ¬ P ^ (∑ i ∈ range n, (GlueConductor.ramCard L P i - 1) + 1) ∣
              differentIdeal ℤ (𝓞 L) := by
  intro L _ _ _ x hx P _ hP
  exact hilbertDifferentAt_of_monogenic L x hx P hP

/-- At exponent zero, exact prime-power divisibility really means the prime does not divide. -/
theorem exponent_zero_iff (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    multiplicity P (differentIdeal ℤ (𝓞 L)) = 0 ↔ ¬ P ∣ differentIdeal ℤ (𝓞 L) := by
  simpa using multiplicity_different_eq_iff L P hP 0

/-- The chosen cutoff is irrelevant once the actual global groups are trivial there. -/
theorem sum_independent_of_triviality_witness (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) {m n : ℕ}
    (hm : GlueConductor.ramGroup L P m = ⊥) (hn : GlueConductor.ramGroup L P n = ⊥) :
    ramificationSum L P m = ramificationSum L P n :=
  (finsum_ramCard_sub_one_eq_sum L P hm).symm.trans (finsum_ramCard_sub_one_eq_sum L P hn)

/-- The zero prime is excluded from the arithmetic target, but its filtration causes no false
nontriviality assertion: every positive power has zero-ideal inertia, which is trivial. -/
theorem zero_prime_filtration (L : Type*) [Field L] [NumberField L] (i : ℕ) :
    GlueConductor.ramGroup L (⊥ : Ideal (𝓞 L)) i = ⊥ := by
  let := ringOfIntegers_faithfulSMul L
  simp [GlueConductor.ramGroup]

/-- The ring of integers of ℚ is generated over ℤ by zero. This supplies, rather than assumes,
the monogenic input for the degree-one regression check. -/
theorem rational_integer_ring_generated_zero :
    Algebra.adjoin ℤ {(0 : 𝓞 ℚ)} = ⊤ := by
  apply eq_top_iff.mpr
  intro y _
  have hy : algebraMap ℤ (𝓞 ℚ) (Rat.ringOfIntegersEquiv y) = y :=
    Rat.ringOfIntegersEquiv.injective (by simp)
  simpa only [hy] using
    ((Algebra.adjoin ℤ {(0 : 𝓞 ℚ)}).algebraMap_mem (Rat.ringOfIntegersEquiv y))

/-- Every nonzero prime over ℚ satisfies the exact global target with the witness `n=0` and
exponent zero. The automorphism group, derivative-product and range are all trivial here. -/
theorem rational_exact_zero_case (P : Ideal (𝓞 ℚ)) [P.IsPrime] (hP : P ≠ ⊥) :
    GlueConductor.ramGroup ℚ P 0 = ⊥ ∧
      P ^ (∑ i ∈ range 0, (GlueConductor.ramCard ℚ P i - 1)) ∣ differentIdeal ℤ (𝓞 ℚ) ∧
      ¬ P ^ (∑ i ∈ range 0, (GlueConductor.ramCard ℚ P i - 1) + 1) ∣
        differentIdeal ℤ (𝓞 ℚ) := by
  have hn : GlueConductor.ramGroup ℚ P 0 = ⊥ := Subsingleton.elim _ _
  exact ⟨hn, (multiplicity_different_eq_iff ℚ P hP _).mp
    (multiplicity_different_eq_sum_of_monogenic ℚ 0 rational_integer_ring_generated_zero P hP hn)⟩

/-- A degree-one different is the unit ideal, matching the empty derivative product. -/
theorem rational_different_eq_top : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  have hcard : Fintype.card Gal(ℚ/ℚ) = 1 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    simp
  rw [differentIdeal_eq_span_displacementProd_of_monogenic ℚ 0
    rational_integer_ring_generated_zero]
  simp [hcard]

end ZInQ.Contrib.HilbertDifferent.Checks

#print ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_integralClosure_of_monogenic
#print ZInQ.Contrib.HilbertDifferent.differentIdeal_ringOfIntegersRat_eq
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_integralClosure_of_monogenic
#print axioms ZInQ.Contrib.HilbertDifferent.differentIdeal_ringOfIntegersRat_eq
#print axioms ZInQ.Contrib.HilbertDifferent.powerInertia_eq_comap_of_equivariant_dense
#print axioms ZInQ.Contrib.HilbertDifferent.ramCard_eq_card_powerInertia_stabilizer
#print ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_of_monogenic
#print ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_of_multiplicity_finsum
#print ZInQ.Contrib.HilbertDifferent.Checks.exact_global_shape_with_generator
#print axioms ZInQ.Contrib.HilbertDifferent.exists_forall_subgroup_eq_iInf
#print axioms ZInQ.Contrib.HilbertDifferent.iInf_powerInertia_eq_bot
#print axioms ZInQ.Contrib.HilbertDifferent.exists_forall_powerInertia_eq_bot
#print axioms ZInQ.Contrib.HilbertDifferent.exists_forall_ramGroup_eq_bot
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_of_isUnramifiedAt
#print axioms ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_of_monogenic
#print axioms ZInQ.Contrib.HilbertDifferent.sum_displacementMultiplicity_eq_sum_powerInertiaCard
#print axioms ZInQ.Contrib.HilbertDifferent.Checks.exact_global_shape_with_generator
#print axioms ZInQ.Contrib.HilbertDifferent.Checks.rational_exact_zero_case
#print axioms ZInQ.Contrib.HilbertDifferent.Checks.rational_different_eq_top
