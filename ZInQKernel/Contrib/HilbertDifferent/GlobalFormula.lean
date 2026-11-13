import ZInQKernel.Contrib.HilbertDifferent.LocalizationGroup
import ZInQKernel.Contrib.HilbertDifferent.Local

/-!
# GLOBAL Hilbert different formula through legitimate prime localization

This proves the original `GlueConductor.HilbertDifferentFormula`. For each
nonzero prime of a Galois number field, the actual decomposition fixed field
provides a unique-prime, finite DVR localization. The already proved monogenic
integral-closure Hilbert theorem is applied with the unchanged original fields,
not with unconstructed completions. The localized/global different coefficient
is the frozen `DecompositionFieldDifferent` supplier's proved identity. The
new group equivalence and all-power congruence comparison identify every lower
ramification group with the original global group, without a degree factor.

All original PR55 sources and its historical global-open evidence are retained.
No assumed Hilbert formula, `Fact`, completed-different premise, registry edit,
pin change, or independent acceptance is part of this contribution.
-/

open NumberField Finset
open scoped Pointwise HilbertDifferentLocalization

namespace ZInQ.Contrib.HilbertDifferent

open LocalizationModel

/-- The exact original global Hilbert conclusion, at every nonzero prime, using the actual
finite decomposition-field localization and its proved integral-closure/different comparisons. -/
theorem hilbertDifferentAt_localization (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
      P ^ (ramificationSum L P n) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (ramificationSum L P n + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  let : IsDiscreteValuationRing (baseRing L P) := (localizations_areDVR L P hP).1
  let : IsDiscreteValuationRing (topRing L P) := (localizations_areDVR L P hP).2
  let : PerfectField (IsLocalRing.ResidueField (baseRing L P)) := base_residue_perfect L P hP
  let : FiniteDimensional (decompField L P) L := Module.Finite.right ℚ (decompField L P) L
  obtain ⟨β, hβ⟩ := ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top
    (A := baseRing L P) (B := topRing L P)
  obtain ⟨n, hn, hdiv, hnext⟩ := hilbertDifferentAt_integralClosure_of_monogenic
    (baseRing L P) (↥(decompField L P)) L (topRing L P) β hβ
    (IsLocalRing.maximalIdeal (topRing L P)) (IsDiscreteValuationRing.not_a_field _)
  have hlocal : multiplicity (IsLocalRing.maximalIdeal (topRing L P))
      (differentIdeal (baseRing L P) (topRing L P)) =
      ∑ i ∈ range n, (Nat.card ((IsLocalRing.maximalIdeal (topRing L P) ^ (i + 1)).inertia
        (topRing L P ≃ₐ[baseRing L P] topRing L P)) - 1) :=
    multiplicity_eq_of_dvd_of_not_dvd hdiv hnext
  have hbridge : multiplicity (IsLocalRing.maximalIdeal (topRing L P))
      (differentIdeal (baseRing L P) (topRing L P)) =
      multiplicity P (differentIdeal ℤ (𝓞 L)) :=
    GlobalDifferentTransport.multiplicity_absoluteDifferent_decompositionField_atPrime_eq L P hP
  have hsum : multiplicity P (differentIdeal ℤ (𝓞 L)) = ramificationSum L P n := by
    rw [← hbridge, hlocal]
    apply Finset.sum_congr rfl
    intro i _
    rw [ramCard_eq_card_localization L P hP i]
  exact ⟨n, (ramGroup_eq_bot_iff_localization L P hP n).mpr hn,
    (multiplicity_different_eq_iff L P hP _).mp hsum⟩

/-- Exact closed GLOBAL T20 proposition. There are no outer parameters, universe parameters,
additional hypotheses, assumed literature leaves or `Fact` instances on this provider. -/
theorem hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula := by
  intro L _ _ _ P _ hP
  exact hilbertDifferentAt_localization L P hP

end ZInQ.Contrib.HilbertDifferent
