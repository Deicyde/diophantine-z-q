import ExtendedDVRV003
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.FinitePresentation

/-! # Canonical ring maps and the principal generic open of an extended DVR -/

noncomputable section
set_option autoImplicit false

namespace FiniteExtensionValuation

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

/-- The actual inclusion of the base valuation ring into the extended ring. -/
def baseHom (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) : O →+* w :=
  ((algebraMap K M).comp O.subtype).codRestrict w.toSubring (fun a => by
    change algebraMap K M (a : K) ∈ w
    have h : (a : K) ∈ w.comap (algebraMap K M) := by simpa only [hw] using a.2
    exact h)

@[simp] theorem baseHom_coe (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) (a : O) :
    ((baseHom O w hw a : w) : M) = algebraMap K M (a : K) := rfl

theorem baseHom_injective (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) : Function.Injective (baseHom O w hw) := by
  intro a b h
  apply Subtype.ext
  exact (algebraMap K M).injective (congrArg (fun z : w => (z : M)) h)

instance baseHom_isLocalHom (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) : IsLocalHom (baseHom O w hw) where
  map_nonunit a h := (base_unit_iff O w hw a).2
    ((w.valuation_eq_one_iff (baseHom O w hw a)).1 h)

theorem baseHom_comap_maximalIdeal (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    (IsLocalRing.maximalIdeal w).comap (baseHom O w hw) = IsLocalRing.maximalIdeal O := by
  ext a
  simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr ⟨fun h => IsUnit.of_map (baseHom O w hw) a h, fun h => h.map _⟩

/-- The square of inclusions into the two fraction fields commutes literally. -/
theorem fraction_field_square (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    w.subtype.comp (baseHom O w hw) = (algebraMap K M).comp O.subtype := rfl

/-- The field algebra used for normalization is the actual base inclusion. -/
@[instance_reducible] def extensionFieldAlgebra (O : ValuationSubring K) : Algebra O M :=
  ((algebraMap K M).comp O.subtype).toAlgebra

/-- The extended valuation ring algebra is the actual local inclusion. -/
@[instance_reducible] def extensionRingAlgebra (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) : Algebra O w := (baseHom O w hw).toAlgebra

theorem extensionField_tower (O : ValuationSubring K) :
    letI := extensionFieldAlgebra (M := M) O
    IsScalarTower O K M := by
  letI := extensionFieldAlgebra (M := M) O
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem extensionRing_tower (O : ValuationSubring K) (w : ValuationSubring M)
    (hw : w.comap (algebraMap K M) = O) :
    letI := extensionFieldAlgebra (M := M) O
    letI := extensionRingAlgebra O w hw
    IsScalarTower O w M := by
  letI := extensionFieldAlgebra (M := M) O
  letI := extensionRingAlgebra O w hw
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The fraction field of a DVR is obtained by inverting its actual uniformizer. -/
theorem fraction_field_away (w : ValuationSubring M) [IsDiscreteValuationRing w]
    {π : w} (hπ : Irreducible π) : IsLocalization.Away π M := by
  apply IsLocalization.Away.mk π
  · exact isUnit_iff_ne_zero.2 (fun h => hπ.ne_zero (Subtype.ext h))
  · intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := w) x
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (u⁻¹ : wˣ), ?_⟩
    change ((a : M) / ((u : M) * (π : M) ^ n)) * (π : M) ^ n =
      (a : M) * ((u⁻¹ : wˣ) : M)
    have hπ0 : (π : M) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    have huinv : ((u⁻¹ : wˣ) : M) = (u : M)⁻¹ := map_units_inv w.subtype u
    have hu0 : (u : M) ≠ 0 := (Units.map w.subtype.toMonoidHom u).ne_zero
    rw [huinv]
    field_simp
  · intro a b h
    exact ⟨0, by simpa using (Subtype.ext h : a = b)⟩

end FiniteExtensionValuation
