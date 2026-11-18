import ActualInertiaRestrictionV002

/-!
# The actual restricted valuation lies over the original valuation

Units and the residue characteristic are transported by the genuine
local valuation-ring scalar inclusion. No unrelated finite valuation
model or new valuation class is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ActualValuationRestriction
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma restriction_lies_over (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (L : IntermediateField K Ω) :
    (w.comap L.val.toRingHom).comap (algebraMap K L) = O := by
  rw [ValuationSubring.comap_comap]
  have he : L.val.toRingHom.comp (algebraMap K L) = algebraMap K Ω := by
    ext a
    rfl
  rw [he, hw]

lemma base_valuation_equiv (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) :
    (w.valuation.comap (algebraMap K Ω)).IsEquiv O.valuation := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  rw [Valuation.comap_apply, w.valuation_le_one_iff, O.valuation_le_one_iff]
  change x ∈ w.comap (algebraMap K Ω) ↔ x ∈ O
  rw [hw]

instance scalarInclusion_local (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) :
    IsLocalHom (WildFiniteRestriction.valuationRingMap O w hw) := by
  constructor
  intro a ha
  apply (O.valuation_eq_one_iff a).mpr
  apply (base_valuation_equiv O w hw).eq_one_iff_eq_one.mp
  exact (w.valuation_eq_one_iff (WildFiniteRestriction.valuationRingMap O w hw a)).mp ha

lemma prime_unit_at_restriction (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (L : IntermediateField K Ω) (ℓ : ℕ) (hu : IsUnit (ℓ : O)) :
    IsUnit (ℓ : w.comap L.val.toRingHom) := by
  have h := hu.map (WildFiniteRestriction.valuationRingMap O (w.comap L.val.toRingHom)
    (restriction_lies_over O w hw L))
  simpa only [map_natCast] using h

lemma residue_characteristic_inherited (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (L : IntermediateField K Ω) (p : ℕ)
    [CharP (IsLocalRing.ResidueField O) p] :
    CharP (IsLocalRing.ResidueField (w.comap L.val.toRingHom)) p := by
  let f := IsLocalRing.ResidueField.map
    (WildFiniteRestriction.valuationRingMap O (w.comap L.val.toRingHom) (restriction_lies_over O w hw L))
  constructor
  intro n
  have hi : f (n : IsLocalRing.ResidueField O) = f 0 ↔ (n : IsLocalRing.ResidueField O) = 0 :=
    f.injective.eq_iff
  have hn : (n : IsLocalRing.ResidueField (w.comap L.val.toRingHom)) = 0 ↔
      (n : IsLocalRing.ResidueField O) = 0 := by
    simpa only [map_natCast, map_zero] using hi
  exact hn.trans (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField O) p n)

end ActualValuationRestriction
