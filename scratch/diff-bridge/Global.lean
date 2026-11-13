import Mathlib
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Exponent
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.RamificationGroup

open NumberField IsDedekindDomain

namespace DiffBridge

/-- The image of `𝓞 ℚ` in `ℚ` is the image of `ℤ`. -/
theorem range_algebraMap_ringOfIntegers_rat :
    (algebraMap (𝓞 ℚ) ℚ).range = (algebraMap ℤ ℚ).range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp y.isIntegral_coe
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩

/-- `ℤ → 𝓞 ℚ` is surjective. -/
theorem algebraMap_int_ringOfIntegers_rat_surjective :
    Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
  intro y
  have : (algebraMap (𝓞 ℚ) ℚ y) ∈ (algebraMap ℤ ℚ).range := by
    rw [← range_algebraMap_ringOfIntegers_rat]; exact ⟨y, rfl⟩
  obtain ⟨n, hn⟩ := this
  refine ⟨n, ?_⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 ℚ) ℚ
  rw [← hn, ← IsScalarTower.algebraMap_apply]

variable (L : Type*) [Field L] [NumberField L]

/-- The different of `𝓞 L` over `ℤ` is the different over `𝓞 ℚ`. -/
theorem differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat :
    differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L) := by
  apply IsFractionRing.coeSubmodule_injective (𝓞 L) L
  rw [coeSubmodule_differentIdeal ℤ ℚ, coeSubmodule_differentIdeal (𝓞 ℚ) ℚ]
  congr 1
  ext x
  simp only [Submodule.mem_traceDual, range_algebraMap_ringOfIntegers_rat]

variable {L}

/-- The ramification index of a prime `P` of `𝓞 L` over `ℤ` equals the one over `𝓞 ℚ`. -/
theorem ramificationIdx_int_eq (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ) := by
  have key : Ideal.map (algebraMap ℤ (Localization.AtPrime P)) (Ideal.under ℤ P) =
      Ideal.map (algebraMap (𝓞 ℚ) (Localization.AtPrime P)) (Ideal.under (𝓞 ℚ) P) := by
    rw [IsScalarTower.algebraMap_eq ℤ (𝓞 ℚ) (Localization.AtPrime P), ← Ideal.map_map]
    congr 1
    rw [← Ideal.under_under (B := 𝓞 ℚ) P]
    exact Ideal.map_comap_of_surjective _ algebraMap_int_ringOfIntegers_rat_surjective _
  rw [Ideal.ramificationIdx_def, Ideal.ramificationIdx_def]
  congr 3

/-- A nonzero prime of `𝓞 L`, as a point of the height one spectrum. -/
def toHeightOneSpectrum (P : Ideal (𝓞 L)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    HeightOneSpectrum (𝓞 L) :=
  ⟨P, hP, hP0⟩

/-- Tau Ceti's ramification groups are `GlueConductor.ramGroup`. -/
theorem ramificationGroup_eq_ramGroup [IsGalois ℚ L] (P : Ideal (𝓞 L)) (i : ℕ) :
    P.ramificationGroup (L ≃ₐ[ℚ] L) i = GlueConductor.ramGroup L P i :=
  Ideal.ramificationGroup_def P i

/-- **T20, global (`GlueConductor.HilbertDifferentFormula`).** -/
theorem hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula := by
  intro L _ _ _ P _ hP0
  set w := toHeightOneSpectrum P hP0 with hw
  have hH := HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one
    (K := ℚ) w
  have hwP : w.asIdeal = P := rfl
  rw [hwP] at hH
  have hPtop : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  have : FaithfulSMul (L ≃ₐ[ℚ] L) (𝓞 L) := IsGaloisGroup.faithful (𝓞 ℚ)
  obtain ⟨N, hN⟩ := Ideal.exists_forall_ramificationGroup_eq_bot (G := L ≃ₐ[ℚ] L) hPtop
  have hfin : ∑ᶠ i : ℕ, (Nat.card (P.ramificationGroup (L ≃ₐ[ℚ] L) i) - 1) =
      ∑ i ∈ Finset.range N, (GlueConductor.ramCard L P i - 1) := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range N)]
    · rfl
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hle
      apply hi
      rw [hN i (not_lt.mp hle)]
      simp
  rw [hfin, ← differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat] at hH
  have hD0 : differentIdeal ℤ (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  have hF : FiniteMultiplicity P (differentIdeal ℤ (𝓞 L)) := Ideal.finiteMultiplicity hPtop hD0
  refine ⟨N, ?_, ?_, ?_⟩
  · rw [← ramificationGroup_eq_ramGroup]
    exact hN N le_rfl
  · rw [← hH]
    exact pow_multiplicity_dvd _ _
  · apply hF.not_pow_dvd_of_multiplicity_lt
    rw [hH]
    exact Nat.lt_succ_self _

end DiffBridge
