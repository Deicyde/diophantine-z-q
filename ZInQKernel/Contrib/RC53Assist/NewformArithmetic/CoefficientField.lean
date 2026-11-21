import ZInQKernel.Contrib.RC53Assist.NewformArithmetic.BadPrime
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.NumberField

namespace ZInQ.Contrib.RC53Assist.NewformArithmetic

open UpperHalfPlane HeckeRing.GL2

/-- The coefficient field generated using *all* natural indices is the
vendored field generated using positive indices. The added constant
coefficient of a cusp form is zero. -/
theorem adjoin_all_coeffs_eq {M : ℕ} [NeZero M] (F : Newform M 2) :
    IntermediateField.adjoin ℚ (Set.range fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n) =
      TauCeti.CoefficientField F := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero =>
      change (qExpansion 1 F.toCuspForm).coeff 0 ∈ TauCeti.CoefficientField F
      rw [CuspFormClass.qExpansion_coeff_zero F.toCuspForm one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map M)]
      exact zero_mem _
    | succ n => exact TauCeti.coeff_mem_CoefficientField F ⟨n + 1, Nat.succ_pos n⟩
  · refine (TauCeti.CoefficientField_le_iff F _).mpr fun n => ?_
    exact IntermediateField.subset_adjoin ℚ _ ⟨(n : ℕ), rfl⟩

/-- The number-field clause used in the Shimura conjugate-eigenform input,
for the exact adjoin used there. It does not require a character hypothesis. -/
theorem finiteDimensional_adjoin_all_coeffs {M : ℕ} [NeZero M] (F : Newform M 2) :
    FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range fun n : ℕ => (qExpansion 1 F.toCuspForm).coeff n)) := by
  rw [adjoin_all_coeffs_eq F]
  exact (TauCeti.numberField_CoefficientField F le_rfl).to_finiteDimensional

/-- For a trivial-character newform of weight two, an intermediate field
contains all the coefficients once it contains the good-prime coefficients.
The bad-prime coefficients and the nebentypus values lie in the ground field. -/
theorem coefficientField_le_of_good_primes {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) (K : IntermediateField ℚ ℂ)
    (hgood : ∀ p : ℕ, p.Prime → ¬p ∣ M → (qExpansion 1 F.toCuspForm).coeff p ∈ K) :
    TauCeti.CoefficientField F ≤ K := by
  refine (TauCeti.CoefficientField_le_iff_forall_prime_and_char F K).mpr ⟨?_, ?_⟩
  · intro p hp
    by_cases hpM : p ∣ M
    · have h := bad_prime_weight_two M F hχ p hp hpM
      by_cases hsq : p ^ 2 ∣ M
      · rw [h.1 hsq]
        exact zero_mem _
      · let a := (qExpansion 1 F.toCuspForm).coeff p
        have ha : a ^ 2 = 1 := h.2 hsq
        have haz : (a + 1) * (a - 1) = 0 := by
          rw [← sq_sub_sq, ha, one_pow, sub_self]
        change a ∈ K
        rcases mul_eq_zero.mp haz with hm1 | h1
        · have hh : a = -1 := eq_neg_of_add_eq_zero_left hm1
          rw [hh]
          exact neg_mem (one_mem _)
        · rw [sub_eq_zero.mp h1]
          exact one_mem _
    · exact hgood p hp hpM
  · intro u
    rw [hχ]
    simp

/-- If the good-prime coefficients outside `S` are rational, precisely the
remaining good-prime coefficients generate the full coefficient field. This
applies to the finite exceptional set in the divisor-level extraction. -/
theorem coefficientField_eq_adjoin_exceptional_good_primes {M : ℕ} [NeZero M]
    (F : Newform M 2) (hχ : F.χ = 1) (S : Finset ℕ)
    (hS : ∀ p : ℕ, p.Prime → ¬p ∣ M → p ∉ S →
      ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff p = (b : ℂ)) :
    TauCeti.CoefficientField F = IntermediateField.adjoin ℚ
      {a : ℂ | ∃ p : ℕ, p ∈ S ∧ p.Prime ∧ ¬p ∣ M ∧
        a = (qExpansion 1 F.toCuspForm).coeff p} := by
  apply le_antisymm
  · apply coefficientField_le_of_good_primes F hχ
    intro p hp hpM
    by_cases hmem : p ∈ S
    · exact IntermediateField.subset_adjoin ℚ _ ⟨p, hmem, hp, hpM, rfl⟩
    · obtain ⟨b, hb⟩ := hS p hp hpM hmem
      rw [hb]
      exact IntermediateField.algebraMap_mem _ b
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, _, hp, _, rfl⟩
    exact TauCeti.coeff_mem_CoefficientField F ⟨p, hp.pos⟩

/-- With rationality at all good primes there is no exceptional generator. -/
theorem coefficientField_eq_bot_of_good_prime_rat {M : ℕ} [NeZero M] (F : Newform M 2)
    (hχ : F.χ = 1) (hgood : ∀ p : ℕ, p.Prime → ¬p ∣ M →
      ∃ b : ℚ, (qExpansion 1 F.toCuspForm).coeff p = (b : ℂ)) :
    TauCeti.CoefficientField F = ⊥ := by
  apply bot_unique (coefficientField_le_of_good_primes F hχ ⊥ ?_)
  intro p hp hpM
  obtain ⟨b, hb⟩ := hgood p hp hpM
  exact IntermediateField.mem_bot.mpr ⟨b, hb.symm⟩

end ZInQ.Contrib.RC53Assist.NewformArithmetic
