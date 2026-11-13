import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Local inclusions with a common fraction field

A local inclusion of a valuation ring into another ring embedded in the same fraction field
is surjective. In particular, a local inclusion of DVRs with a common fraction field is an
isomorphism. The target does not need to be a DVR.

The proof uses `ValuationRing.isInteger_or_isInteger`: an element of the fraction field or its
inverse lies in the source. In the inverse case, the corresponding source element maps to a
unit in the target, so `IsLocalHom` reflects that unit back to the source. The scalar-tower
identity identifies the actual algebra maps; equality of valuation rings is not assumed.

Source provenance: the proof below is an original connecting argument using Mathlib 4.35.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`. The valuation-ring primitive is in
`Mathlib/RingTheory/Valuation/ValuationRing.lean` (Adam Topaz); fraction-map injectivity is in
`Mathlib/RingTheory/Localization/FractionRing.lean` (Kenny Lau, Mario Carneiro, Johan Commelin,
Amelia Livingston, Anne Baanen); unit reflection is in `Mathlib/Algebra/Group/Units/Hom.lean`.
No external proof is ported. This module supplies only the inclusion bridge, not the DVR or
fraction-field instances for any particular Kummer subring, and makes no assembled T2 claim.
-/

namespace ZInQ.Contrib.Abhyankar

section ValuationRing

variable (R S F : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
  [CommRing S] [Algebra R S] [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra S F] [IsFractionRing S F] [IsScalarTower R S F]
  [IsLocalHom (algebraMap R S)]

include F

/-- A local algebra map out of a valuation ring is bijective when the source and target
have the same fraction field and their algebra maps into that field form a scalar tower. -/
theorem algebraMap_bijective_of_valuationRing : Function.Bijective (algebraMap R S) := by
  have hS : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  constructor
  · intro a b hab
    apply IsFractionRing.injective R F
    simpa only [IsScalarTower.algebraMap_apply R S F] using congrArg (algebraMap S F) hab
  · intro s
    by_cases hs : s = 0
    · exact ⟨0, by simp [hs]⟩
    have hsF : algebraMap S F s ≠ 0 := by
      intro h
      apply hs
      exact hS (by simpa only [map_zero] using h)
    rcases ValuationRing.isInteger_or_isInteger R (algebraMap S F s) with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨r, hS ?_⟩
      simpa only [← IsScalarTower.algebraMap_apply R S F] using hr
    · have hmul : algebraMap R S r * s = 1 := by
        apply hS
        rw [map_mul, ← IsScalarTower.algebraMap_apply R S F, hr,
          inv_mul_cancel₀ hsF, map_one]
      have hrUnit : IsUnit r :=
        isUnit_of_map_unit (algebraMap R S) r (IsUnit.of_mul_eq_one s hmul)
      obtain ⟨u, hu⟩ := hrUnit
      refine ⟨(u⁻¹ : Rˣ), ?_⟩
      have huS : algebraMap R S (u : R) * s = 1 := by simpa only [hu] using hmul
      calc
        algebraMap R S (u⁻¹ : Rˣ) =
            algebraMap R S (u⁻¹ : Rˣ) * (algebraMap R S (u : R) * s) := by rw [huS, mul_one]
        _ = s := by rw [← mul_assoc, ← map_mul, u.inv_mul, map_one, one_mul]

end ValuationRing

section DVR

variable (R S F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra S F] [IsFractionRing S F] [IsScalarTower R S F]
  [IsLocalHom (algebraMap R S)]

include F

/-- DVR specialization of `algebraMap_bijective_of_valuationRing`.
No local-ring or DVR assumption on the target is needed. -/
theorem algebraMap_bijective_of_dvr : Function.Bijective (algebraMap R S) :=
  algebraMap_bijective_of_valuationRing R S F

/-- The algebra equivalence associated to a local DVR inclusion with a common fraction field.
Its forward map is the given `algebraMap R S`, not an unrelated ring isomorphism. -/
noncomputable def dvrInclusionAlgEquiv : R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S) (algebraMap_bijective_of_dvr R S F)

/-- The inclusion equivalence has the prescribed forward map. -/
@[simp]
theorem dvrInclusionAlgEquiv_apply (r : R) :
    dvrInclusionAlgEquiv R S F r = algebraMap R S r := rfl

/-- The inverse equivalence preserves the prescribed embeddings in the common fraction field. -/
@[simp]
theorem algebraMap_dvrInclusionAlgEquiv_symm (s : S) :
    algebraMap R F ((dvrInclusionAlgEquiv R S F).symm s) = algebraMap S F s := by
  rw [IsScalarTower.algebraMap_apply R S F]
  change algebraMap S F (dvrInclusionAlgEquiv R S F ((dvrInclusionAlgEquiv R S F).symm s)) = _
  rw [AlgEquiv.apply_symm_apply]

end DVR

end ZInQ.Contrib.Abhyankar
