import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.CurveAtPlace
import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.SplitRoot
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Defs

/-! The very same twist change of variables is integral at the selected place,
and its reduction is the base change of a change of variables over the prime field. -/

noncomputable section

open IsLocalRing WeierstrassCurve ZInQ.Contrib.CloudB3RC53.GenusOdd
open ZInQ.Contrib.ChebFD.C10 (Zbar Qbar GQ)
open scoped Classical

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

/-- The integral twist change is defined by a unit at the exact place, and the
choice of split root in the prime field is the specialization of the global root. -/
theorem twistVC_at_place {D : ℤ} (hD : ¬ (p : ℤ) ∣ D) (hplus : legendreSym p D = 1)
    (s : Zbar) (hs : s ^ 2 = (D : Zbar)) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 = (D : ZMod p) ∧
      ∃ T : VariableChange v.valuationRing.valuation.valuationSubring,
        T.map (algebraMap v.valuationRing.valuation.valuationSubring Qbar) = twistVC (s : Qbar) ∧
        T.map (residue v.valuationRing.valuation.valuationSubring) =
          (twistVC a).map (algebraMap (ZMod p)
            (ResidueField v.valuationRing.valuation.valuationSubring)) := by
  obtain ⟨a, ha, ha2, har⟩ := v.split_root_over_primeField hD hplus s hs
  let t := v.localValuationEquiv (algebraMap Zbar v.localRing.toSubring s)
  have ht : (t : Qbar) = (s : Qbar) := rfl
  have hr : residue v.valuationRing.valuation.valuationSubring t =
      algebraMap (ZMod p) (ResidueField v.valuationRing.valuation.valuationSubring) a := by
    change v.valuationResidueEquiv (Ideal.Quotient.mk v.prime s) = _
    rw [← har]
    let j := v.valuationResidueEquiv.toRingHom.comp (algebraMap (ZMod p) (Zbar ⧸ v.prime))
    change j a = _
    obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
    simp only [map_intCast]
  have hu : IsUnit t := (residue_ne_zero_iff_isUnit t).mp (by
    rw [hr]
    exact (map_ne_zero (algebraMap (ZMod p) (ResidueField v.valuationRing.valuation.valuationSubring))).mpr ha)
  let u := hu.unit
  have hv : (u : v.valuationRing.valuation.valuationSubring) = t := hu.unit_spec
  have hs0 : (s : Qbar) ≠ 0 := by
    rw [← ht, ← hv]
    exact (u.isUnit.map (algebraMap v.valuationRing.valuation.valuationSubring Qbar)).ne_zero
  refine ⟨a, ha, ha2, ⟨u⁻¹, 0, 0, 0⟩, ?_, ?_⟩
  · rw [twistVC, dite_eq_right hs0]
    ext <;> simp [VariableChange.map, hv, ht]
  · rw [twistVC, dite_eq_right ha]
    ext <;> simp [VariableChange.map, hv, hr]

/-- Scaling by any power of the integral unit does not change the valuation
of a coordinate. In the split identification poles stay poles. -/
theorem twist_unit_valuation (u : v.valuationRing.valuation.valuationSubringˣ) (m : ℕ) (x : Qbar) :
    v.valuationRing.valuation (((u : v.valuationRing.valuation.valuationSubring) : Qbar) ^ m * x) =
      v.valuationRing.valuation x := by
  have h (a : v.valuationRing.valuation.valuationSubringˣ) :
      v.valuationRing.valuation ((a : v.valuationRing.valuation.valuationSubring) : Qbar) = 1 := by
    apply le_antisymm a.val.property
    apply le_of_not_gt
    exact fun hlt => ((IsLocalRing.mem_maximalIdeal (a : v.valuationRing.valuation.valuationSubring)).mp
      ((Valuation.mem_maximalIdeal_iff (v := v.valuationRing.valuation)).mpr hlt)) a.isUnit
  rw [map_mul, map_pow, h u, one_pow, one_mul]

/-- On an integral coordinate, a scale factor from the unit change of variables
reduces to the same power of the residue unit. -/
theorem twist_unit_residue (u : v.valuationRing.valuation.valuationSubringˣ) (m : ℕ) (x : Qbar)
    (hx : v.valuationRing.valuation x ≤ 1) :
    residue v.valuationRing.valuation.valuationSubring
      ⟨((u : v.valuationRing.valuation.valuationSubring) : Qbar) ^ m * x,
        by change v.valuationRing.valuation _ ≤ 1; rwa [v.twist_unit_valuation u m x]⟩ =
      (residue v.valuationRing.valuation.valuationSubring (u : v.valuationRing.valuation.valuationSubring)) ^ m *
        residue v.valuationRing.valuation.valuationSubring ⟨x, hx⟩ := by
  let Rₚ := v.valuationRing.valuation.valuationSubring
  have h : (⟨((u : Rₚ) : Qbar) ^ m * x,
      by change v.valuationRing.valuation _ ≤ 1; rwa [v.twist_unit_valuation u m x]⟩ : Rₚ) =
      (u : Rₚ) ^ m * ⟨x, hx⟩ := Subtype.ext rfl
  rw [h, map_mul, map_pow]

/-- On any integral equation the split change specializes to the prime-field
change acting on the reduced equation. Together with the unit coordinate
formulas, this gives the affine specialization rule for the twist. -/
theorem twistVC_reduction_equation {D : ℤ} (hD : ¬ (p : ℤ) ∣ D)
    (hplus : legendreSym p D = 1) (s : Zbar) (hs : s ^ 2 = (D : Zbar))
    (C : WeierstrassCurve v.valuationRing.valuation.valuationSubring) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 = (D : ZMod p) ∧
      ∃ T : VariableChange v.valuationRing.valuation.valuationSubring,
        (T • C).map (algebraMap v.valuationRing.valuation.valuationSubring Qbar) =
          twistVC (s : Qbar) • C.map (algebraMap v.valuationRing.valuation.valuationSubring Qbar) ∧
        (T • C).map (residue v.valuationRing.valuation.valuationSubring) =
          (twistVC a).map (algebraMap (ZMod p)
            (ResidueField v.valuationRing.valuation.valuationSubring)) •
            C.map (residue v.valuationRing.valuation.valuationSubring) := by
  obtain ⟨a, ha, ha2, T, hT, hT'⟩ := v.twistVC_at_place hD hplus s hs
  refine ⟨a, ha, ha2, T, ?_, ?_⟩
  · rw [← map_variableChange, hT]
  · rw [← map_variableChange, hT']

#print axioms twistVC_at_place
#print axioms twist_unit_valuation
#print axioms twist_unit_residue
#print axioms twistVC_reduction_equation

end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
