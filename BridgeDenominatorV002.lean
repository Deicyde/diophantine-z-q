import DirectLocalizedTorsionGenerationV002
import DirectLevelOneGaloisModelV002
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPeriodConversion

/-!
# Cyclotomic coefficients of the actual orbit denominator

The full principal torsion orbit gives a field-valued Vandermonde series.
Squaring and the proved level-one period conversion recover the exact
period-one coefficients of the actual denominator. Coefficient conjugation
constructs a genuine level-one form; its series is proved nonzero without
assuming that the denominator itself is rational or a constant-term unit.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm BigOperators

namespace BridgeDenominator

open ZInQ.Contrib.HeckePrimeRationality
open DirectTorsionOrbit DirectOrbitInterpolation DirectLocalizedTorsionGeneration

/-- The literal coefficient-field lift of a series whose membership has been proved. -/
def coefficientLift (K : IntermediateField ℚ ℂ) (A : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) : PowerSeries K :=
  PowerSeries.mk (fun n => ⟨A.coeff n, hA n⟩)

/-- Mapping this actual lift back gives every original coefficient. -/
theorem coefficientLift_map (K : IntermediateField ℚ ℂ) (A : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) :
    PowerSeries.map (algebraMap K ℂ) (coefficientLift K A hA) = A := by
  ext n
  simp only [PowerSeries.coeff_map, coefficientLift, PowerSeries.coeff_mk,
    IntermediateField.algebraMap_apply]

/-- Membership of every finite convolution row is preserved in the same field. -/
theorem coefficients_mem_mul (K : IntermediateField ℚ ℂ) (A B : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) (hB : ∀ n : ℕ, B.coeff n ∈ K) :
    ∀ n : ℕ, (A * B).coeff n ∈ K := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact K.sum_mem (fun ij _ => K.mul_mem (hA ij.1) (hB ij.2))

/-- Every actual inverse coset torsion form has principal-period cyclotomic coefficients. -/
theorem orbit_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (i : Fin (orbitLength N)) (n : ℕ) :
    (qExpansion (N : ℝ) (torsionOrbit N hN i)).coeff n ∈ Torsion.coefficientField N := by
  let v := ThetaFiveTorsion.act (0, 1) (representative N i)⁻¹
  change (qExpansion (N : ℝ) (Torsion.torsionLogDerivative N v.1 v.2)).coeff n ∈ _
  exact AllLevelIntegerRows.torsion_coeff_mem N v.1 v.2
    (AllLevelForms.good_act (base_good N hN) (representative N i)⁻¹) n

/-- The actual Vandermonde denominator's full principal-period series lies in the cyclotomic field. -/
theorem orbit_denominator_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∀ n : ℕ, (qExpansion (N : ℝ) (orbitDenominator N hN)).coeff n ∈ Torsion.coefficientField N := by
  let K := Torsion.coefficientField N
  let F : Fin (orbitLength N) → PowerSeries K := fun i =>
    coefficientLift K (qExpansion (N : ℝ) (torsionOrbit N hN i))
      (orbit_coefficients_mem N hN i)
  let φ : K →+* ℂ := algebraMap K ℂ
  have hF (i : Fin (orbitLength N)) : PowerSeries.map φ (F i) =
      qExpansion (N : ℝ) (torsionOrbit N hN i) := coefficientLift_map K _ _
  have hm : (PowerSeries.map φ).mapMatrix (Matrix.vandermonde F) =
      Matrix.vandermonde (fun i => qExpansion (N : ℝ) (torsionOrbit N hN i)) := by
    funext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.vandermonde_apply, map_pow, hF]
  have hmap : PowerSeries.map φ (Matrix.det (Matrix.vandermonde F)) =
      qExpansion (N : ℝ) (orbitDenominator N hN) := by
    rw [(PowerSeries.map φ).map_det, hm, orbitDenominator,
      DirectWeightedDeterminant.qExpansion_vandermondeForm _
        (by exact_mod_cast NeZero.pos N) (principal_period N)]
  intro n
  have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) hmap
  rw [PowerSeries.coeff_map] at hn
  rw [← hn]
  exact ((Matrix.det (Matrix.vandermonde F)).coeff n).property

/-- The constructed level-one square has cyclotomic coefficients at the actual principal period. -/
theorem denominator_coefficients_mem_period (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∀ n : ℕ, (qExpansion (N : ℝ) (denominator N hN)).coeff n ∈ Torsion.coefficientField N := by
  have he : ⇑(denominator N hN) = ⇑(orbitDenominator N hN) * ⇑(orbitDenominator N hN) := by
    funext τ
    rw [denominator_coe]
    simp only [Pi.mul_apply, pow_two]
  rw [he, ModularForm.qExpansion_mul_coe (by exact_mod_cast NeZero.pos N)
    (principal_period N) (orbitDenominator N hN) (orbitDenominator N hN)]
  exact coefficients_mem_mul _ _ _
    (orbit_denominator_coefficients_mem N hN) (orbit_denominator_coefficients_mem N hN)

/-- The genuine restriction of a level-one form to the exact Gamma-one space. -/
def restrictLevelOne (N : ℕ) (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  ModularForm.restrict (Subgroup.map_le_range _ _) f

/-- Restriction changes no analytic value. -/
theorem restrictLevelOne_coe (N : ℕ) (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    ⇑(restrictLevelOne N k f) = ⇑f := rfl

/-- Actual period conversion produces every period-one coefficient in the same field. -/
theorem denominator_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ∀ n : ℕ, (qExpansion 1 (denominator N hN)).coeff n ∈ Torsion.coefficientField N :=
  (AllLevelPeriodConversion.coefficient_field_iff N
    (restrictLevelOne N _ (denominator N hN)) (Torsion.coefficientField N)).mp
      (denominator_coefficients_mem_period N hN)

/-- The actual denominator series is nonzero; no constant coefficient is guessed. -/
theorem denominator_qExpansion_ne_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    qExpansion 1 (denominator N hN) ≠ 0 := by
  intro hq
  exact denominator_ne_zero N hN
    ((ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_SL _).mp hq)

/-- The exact field-valued series of the constructed denominator. -/
def denominatorSeries (N : ℕ) [NeZero N] (hN : 3 ≤ N) : PowerSeries (Torsion.coefficientField N) :=
  coefficientLift _ (qExpansion 1 (denominator N hN)) (denominator_coefficients_mem N hN)

/-- The level-one coefficient model constructs the actual conjugate denominator. -/
def conjugateDenominator (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) :
    ModularForm 𝒮ℒ (2 * orbitWeight N) :=
  Classical.choose (DirectLevelOneGaloisModel.exists_unique_coefficient_conjugate _ _ σ
    (denominator N hN) (denominator_coefficients_mem N hN))

/-- Its coefficients are the actual field automorphism applied to the derived denominator coefficients. -/
theorem conjugateDenominator_coeff (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) (n : ℕ) :
    (qExpansion 1 (conjugateDenominator N hN σ)).coeff n =
      (σ (⟨(qExpansion 1 (denominator N hN)).coeff n,
        denominator_coefficients_mem N hN n⟩ : Torsion.coefficientField N) : ℂ) :=
  (Classical.choose_spec (DirectLevelOneGaloisModel.exists_unique_coefficient_conjugate _ _ σ
    (denominator N hN) (denominator_coefficients_mem N hN))).1 n

/-- The conjugate denominator remains in the same coefficient field. -/
theorem conjugateDenominator_coefficients_mem (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) (n : ℕ) :
    (qExpansion 1 (conjugateDenominator N hN σ)).coeff n ∈ Torsion.coefficientField N := by
  rw [conjugateDenominator_coeff]
  exact (σ _).property

/-- Automorphism injectivity proves nonvanishing of the entire conjugate series. -/
theorem conjugateDenominator_qExpansion_ne_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (σ : Torsion.coefficientField N ≃ₐ[ℚ] Torsion.coefficientField N) :
    qExpansion 1 (conjugateDenominator N hN σ) ≠ 0 := by
  intro hzero
  apply denominator_qExpansion_ne_zero N hN
  ext n
  have hs := conjugateDenominator_coeff N hN σ n
  rw [hzero, map_zero] at hs
  have hk : σ (⟨(qExpansion 1 (denominator N hN)).coeff n,
      denominator_coefficients_mem N hN n⟩ : Torsion.coefficientField N) = 0 :=
    Subtype.ext hs.symm
  have hz := σ.injective (hk.trans (map_zero σ).symm)
  exact congrArg (fun z : Torsion.coefficientField N => (z : ℂ)) hz

end BridgeDenominator
