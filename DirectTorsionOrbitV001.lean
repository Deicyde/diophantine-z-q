import DirectTorsionSeparatorV004
import DirectWeightedDeterminantV007

/-!
# A nonzero torsion-orbit denominator at every level at least three

The family is indexed by all actual Gamma-one cosets in the integral
modular group. Its entries are genuine principal-level weight-one forms.
Their pairwise distinct expansions are proved from the exact stabilizer,
so the homogeneous Vandermonde denominator is constructed and nonzero.
No cusp-form spanning or arithmetic basis is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace DirectTorsionOrbit

open ZInQ.Contrib.HeckePrimeRationality

/-- Finiteness here is derived from the actual congruence subgroup. -/
def cosetFintype (N : ℕ) [NeZero N] : Fintype (SL(2, ℤ) ⧸ Gamma1 N) := by
  letI : (Gamma1 N).FiniteIndex := (Gamma1_is_congruence N).finiteIndex
  exact Fintype.ofFinite (SL(2, ℤ) ⧸ Gamma1 N)

/-- The length of the complete actual coset orbit. -/
def orbitLength (N : ℕ) [NeZero N] : ℕ :=
  @Fintype.card (SL(2, ℤ) ⧸ Gamma1 N) (cosetFintype N)

/-- A finite enumeration of that exact quotient, not an asserted modular-form basis. -/
def orbitEquiv (N : ℕ) [NeZero N] : (SL(2, ℤ) ⧸ Gamma1 N) ≃ Fin (orbitLength N) := by
  letI := cosetFintype N
  exact Fintype.equivFin (SL(2, ℤ) ⧸ Gamma1 N)

/-- The integral representative used for an entry of the finite orbit. -/
def representative (N : ℕ) [NeZero N] (i : Fin (orbitLength N)) : SL(2, ℤ) :=
  Quotient.out ((orbitEquiv N).symm i)

/-- The primitive row (0,1) is admissible at every level at least three. -/
theorem base_good (N : ℕ) [NeZero N] (hN : 3 ≤ N) : AllLevelForms.Good N (0, 1) := by
  have hdiv : ¬ (N : ℤ) ∣ 1 := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) (by omega : 1 < N))
  exact fun h => hdiv h.2

/-- Each actual inverse coset translate is bundled with its genuine principal-level fields. -/
def torsionOrbit (N : ℕ) [NeZero N] (hN : 3 ≤ N) (i : Fin (orbitLength N)) :
    ModularForm ((Gamma N).map (mapGL ℝ)) 1 :=
  let v := ThetaFiveTorsion.act (0, 1) (representative N i)⁻¹
  AllLevelPrincipal.principalForm N (NeZero.pos N) v.1 v.2
    (AllLevelForms.good_act (base_good N hN) (representative N i)⁻¹)

/-- The orbit entry is precisely the original analytic torsion function slashed by its matrix. -/
theorem torsionOrbit_coe (N : ℕ) [NeZero N] (hN : 3 ≤ N) (i : Fin (orbitLength N)) :
    ⇑(torsionOrbit N hN i) =
      AllLevelForms.F N (0, 1) ∣[(1 : ℤ)] (representative N i)⁻¹ := by
  change AllLevelForms.F N (ThetaFiveTorsion.act (0, 1) (representative N i)⁻¹) = _
  exact (AllLevelForms.F_slash (NeZero.pos N) (representative N i)⁻¹ (0, 1) (base_good N hN)).symm

/-- The exact positive principal period, derived from the actual principal group. -/
theorem principal_period (N : ℕ) :
    (N : ℝ) ∈ ((Gamma N).map (mapGL ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩

/-- The complete orbit has pairwise distinct actual principal-period expansions. -/
theorem torsionOrbit_qExpansion_injective (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    Function.Injective (fun i => qExpansion (N : ℝ) (torsionOrbit N hN i)) := by
  intro i j hq
  have hforms : torsionOrbit N hN i = torsionOrbit N hN j :=
    ModularForm.qExpansion_injective (by exact_mod_cast NeZero.pos N) (principal_period N) hq
  have hf := congrArg (fun f : ModularForm ((Gamma N).map (mapGL ℝ)) 1 => ⇑f) hforms
  rw [torsionOrbit_coe, torsionOrbit_coe] at hf
  have hmem := (DirectTorsionSeparator.torsion_slash_eq_iff N hN
    (representative N i)⁻¹ (representative N j)⁻¹).mp hf
  have hrepr : (QuotientGroup.mk (representative N i) : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk (representative N j) := by
    apply Quotient.sound
    simpa only [QuotientGroup.leftRel_apply, inv_inv] using hmem
  have hcosets : (orbitEquiv N).symm i = (orbitEquiv N).symm j := by
    simpa only [representative, Quotient.out_eq] using hrepr
  exact (orbitEquiv N).symm.injective hcosets

/-- A genuine homogeneous principal-level denominator, built from the complete orbit. -/
def orbitDenominator (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ModularForm ((Gamma N).map (mapGL ℝ))
      (∑ j : Fin (orbitLength N), (j : ℤ)) :=
  DirectWeightedDeterminant.vandermondeForm (torsionOrbit N hN)

/-- The denominator is nonzero without a basis or spanning hypothesis. -/
theorem orbitDenominator_ne_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    orbitDenominator N hN ≠ 0 :=
  DirectWeightedDeterminant.vandermondeForm_ne_zero (torsionOrbit N hN)
    (by exact_mod_cast NeZero.pos N) (principal_period N)
    (torsionOrbit_qExpansion_injective N hN)

end DirectTorsionOrbit
