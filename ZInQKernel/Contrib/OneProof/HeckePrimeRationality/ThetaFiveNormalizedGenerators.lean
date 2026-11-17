import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveTorsionCoefficients
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SharpLevelFiveBound

/-!
# Normalized weight-one generators at level five

These are actual analytic modular forms constructed from the torsion-theta
quotients. Their first two coefficients and the diamond-two action are proved
from the explicit coefficient formulas. This file does not assume a basis,
Hecke rationality, or a coefficient-field descent theorem.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.NormalizedFive

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open ThetaFiveTorsion ThetaFiveTorsionCoefficients

abbrev MF (k : ℤ) := ModularForm ((Gamma1 5).map (mapGL ℝ)) k

/-- The actual coefficient functional at the width-one cusp. -/
def coefficient (k : ℤ) (n : ℕ) : MF k →ₗ[ℂ] ℂ :=
  (PowerSeries.coeff n).comp
    (TauCeti.ModularForm.qExpansionLinearMap one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map 5) k)

@[simp]
lemma coefficient_apply (k : ℤ) (n : ℕ) (f : MF k) :
    coefficient k n f = (qExpansion 1 f).coeff n := by
  rw [coefficient, LinearMap.comp_apply, TauCeti.ModularForm.qExpansionLinearMap_apply]

/-- The two torsion forms with labels one and two. -/
def fOne : MF 1 := torsionForm 1 (by decide)
def fTwo : MF 1 := torsionForm 2 (by decide)

/-- Constant and first coefficients of a torsion form. -/
def c (b : ℤ) : ℂ := (w b + 1) / (2 * (w b - 1))
def d (b : ℤ) : ℂ := (w b)⁻¹ - w b

lemma coefficient_torsion (b : ℤ) (hb : ¬ (5 : ℤ) ∣ b) (n : ℕ) :
    coefficient 1 n (torsionForm b hb) =
      (qExpansion 1 (torsionLogDerivative 0 b)).coeff n := rfl

lemma coefficient_fOne_zero : coefficient 1 0 fOne = c 1 :=
  torsion_coeff_zero 1 (by decide)
lemma coefficient_fTwo_zero : coefficient 1 0 fTwo = c 2 :=
  torsion_coeff_zero 2 (by decide)
lemma coefficient_fOne_one : coefficient 1 1 fOne = d 1 :=
  torsion_coeff_one 1 (by decide)
lemma coefficient_fTwo_one : coefficient 1 1 fTwo = d 2 :=
  torsion_coeff_one 2 (by decide)

lemma zeta_ne_zero : zetaFive ≠ 0 := by
  simpa [w] using w_ne_zero 1

lemma zeta_ne_one : zetaFive ≠ 1 := by
  intro h
  have hw : w 1 = 1 := by simpa [w] using h
  exact (by decide : ¬ (5 : ℤ) ∣ 1) ((w_eq_one_iff 1).mp hw)

lemma zeta_sq_ne_one : zetaFive ^ 2 ≠ 1 := by
  intro h
  have hw : w 2 = 1 := by simpa [w] using h
  exact (by decide : ¬ (5 : ℤ) ∣ 2) ((w_eq_one_iff 2).mp hw)

lemma zeta_pow_five : zetaFive ^ 5 = 1 := by
  have hw : w 5 = 1 := (w_eq_one_iff 5).mpr (by norm_num)
  simpa [w] using hw

lemma cyclotomic_relation :
    zetaFive ^ 4 + zetaFive ^ 3 + zetaFive ^ 2 + zetaFive + 1 = 0 := by
  have hmul : (zetaFive - 1) *
      (zetaFive ^ 4 + zetaFive ^ 3 + zetaFive ^ 2 + zetaFive + 1) = 0 := by
    calc
      _ = zetaFive ^ 5 - 1 := by ring
      _ = 0 := by rw [zeta_pow_five]; ring
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr zeta_ne_one)

/-- The first-two-coefficient determinant is exactly a rational unit. -/
lemma seed_determinant : c 1 * d 2 - c 2 * d 1 = -(1 / 2 : ℂ) := by
  simp only [c, d, w, zpow_one, zpow_ofNat]
  field_simp [zeta_ne_zero, sub_ne_zero.mpr zeta_ne_one, sub_ne_zero.mpr zeta_sq_ne_one]
  linear_combination (1 - zetaFive ^ 2) * zeta_pow_five

lemma seed_constant_square_sum : c 1 ^ 2 + c 2 ^ 2 = -(1 / 2 : ℂ) := by
  simp only [c, w, zpow_one, zpow_ofNat]
  field_simp [zeta_ne_zero, sub_ne_zero.mpr zeta_ne_one, sub_ne_zero.mpr zeta_sq_ne_one]
  linear_combination 4 * (zetaFive - 1) * zeta_pow_five

lemma seed_mixed_sum : c 1 * d 1 + c 2 * d 2 = -(3 / 2 : ℂ) := by
  simp only [c, d, w, zpow_one, zpow_ofNat]
  field_simp [zeta_ne_zero, sub_ne_zero.mpr zeta_ne_one, sub_ne_zero.mpr zeta_sq_ne_one]
  linear_combination (1 - zetaFive ^ 2) * zeta_pow_five

lemma seed_first_square_sum : d 1 ^ 2 + d 2 ^ 2 = -(5 : ℂ) := by
  simp only [d, w, zpow_one, zpow_ofNat]
  field_simp [zeta_ne_zero]
  linear_combination (zetaFive + zetaFive ^ 3) * zeta_pow_five + cyclotomic_relation

/-- Normalized zero-constant generator. -/
def A : MF 1 := (2 * c 2) • fOne - (2 * c 1) • fTwo

/-- Normalized constant-one generator with first coefficient zero. -/
def B : MF 1 := (-2 * d 2) • fOne + (2 * d 1) • fTwo

lemma A_coeff_zero : coefficient 1 0 A = 0 := by
  simp only [A, map_sub, map_smul, smul_eq_mul,
    coefficient_fOne_zero, coefficient_fTwo_zero]
  ring

lemma A_coeff_one : coefficient 1 1 A = 1 := by
  simp only [A, map_sub, map_smul, smul_eq_mul,
    coefficient_fOne_one, coefficient_fTwo_one]
  linear_combination -2 * seed_determinant

lemma B_coeff_zero : coefficient 1 0 B = 1 := by
  simp only [B, map_add, map_smul, smul_eq_mul,
    coefficient_fOne_zero, coefficient_fTwo_zero]
  linear_combination -2 * seed_determinant

lemma B_coeff_one : coefficient 1 1 B = 0 := by
  simp only [B, map_add, map_smul, smul_eq_mul,
    coefficient_fOne_one, coefficient_fTwo_one]
  ring

/-- Two weight-one forms agreeing in their first two coefficients agree
as actual analytic forms. The sharp bound supplies the proof. -/
lemma eq_of_first_two (f g : MF 1)
    (h0 : coefficient 1 0 f = coefficient 1 0 g)
    (h1 : coefficient 1 1 f = coefficient 1 1 g) : f = g := by
  apply sub_eq_zero.mp
  apply CoeffRational.SharpLevelFiveBound.eq_zero_of_coeff_eq_zero 1 (by norm_num)
  intro n hn
  have hn' : n = 0 ∨ n = 1 := by norm_num at hn; omega
  change coefficient 1 n (f - g) = 0
  rw [map_sub]
  rcases hn' with rfl | rfl
  · exact sub_eq_zero.mpr h0
  · exact sub_eq_zero.mpr h1

/-- A determinant-one representative of the non-sign class two. -/
def gammaTwo : SL(2, ℤ) := ⟨!![3, 1; 5, 2], by norm_num [Matrix.det_fin_two]⟩

lemma gammaTwo_mem : gammaTwo ∈ Gamma0 5 := by
  apply CongruenceSubgroup.Gamma0_mem.mpr
  change (5 : ZMod 5) = 0
  decide +kernel

lemma gammaTwo_label : (Gamma0Map 5).toHomUnits ⟨gammaTwo, gammaTwo_mem⟩ =
    CoeffRational.SharpLevelFiveBound.two := by
  apply Units.ext
  simp [MonoidHom.coe_toHomUnits, Gamma0Map_apply, gammaTwo,
    CoeffRational.SharpLevelFiveBound.two]

/-- The actual diamond-two image of the first torsion form is the second.
The lower-right-entry convention is fixed by the explicit representative. -/
lemma diamond_two_fOne :
    diamondOp 1 CoeffRational.SharpLevelFiveBound.two fOne = fTwo := by
  apply DFunLike.coe_injective
  rw [coe_diamondOp 1 _ ⟨gammaTwo, gammaTwo_mem⟩ gammaTwo_label]
  change F (0, 1) ∣[(1 : ℤ)] gammaTwo = F (0, 2)
  rw [F_slash gammaTwo (0, 1) (by norm_num [Good])]
  have hact : act (0, 1) gammaTwo = (5, 2) := by simp [act, gammaTwo]
  rw [hact]
  funext τ
  simpa using F_shift (a := 0) (b := 2) (by norm_num [Good]) 1 0 τ

lemma diamond_two_fTwo :
    diamondOp 1 CoeffRational.SharpLevelFiveBound.two fTwo = -fOne := by
  rw [← diamond_two_fOne]
  simpa using CoeffRational.SharpLevelFiveBound.diamond_two_twice 1 fOne

/-- The non-sign diamond has the concrete integer matrix on the normalized
weight-one generators; no rational-action theorem is assumed. -/
theorem diamond_two_A :
    diamondOp 1 CoeffRational.SharpLevelFiveBound.two A = (-3 : ℂ) • A - B := by
  apply eq_of_first_two
  · simp only [map_sub, map_smul, smul_eq_mul, A_coeff_zero, B_coeff_zero, mul_zero]
    simp only [A, map_sub, map_smul, smul_eq_mul, diamond_two_fOne,
      diamond_two_fTwo, map_neg, coefficient_fOne_zero, coefficient_fTwo_zero]
    linear_combination 2 * seed_constant_square_sum
  · simp only [map_sub, map_smul, smul_eq_mul, A_coeff_one, B_coeff_one, mul_one, sub_zero]
    simp only [A, map_sub, map_smul, smul_eq_mul, diamond_two_fOne,
      diamond_two_fTwo, map_neg, coefficient_fOne_one, coefficient_fTwo_one]
    linear_combination 2 * seed_mixed_sum

theorem diamond_two_B :
    diamondOp 1 CoeffRational.SharpLevelFiveBound.two B = (10 : ℂ) • A + (3 : ℂ) • B := by
  apply eq_of_first_two
  · simp only [map_add, map_smul, smul_eq_mul, A_coeff_zero, B_coeff_zero, mul_zero, mul_one, zero_add]
    simp only [B, map_add, map_smul, smul_eq_mul, diamond_two_fOne,
      diamond_two_fTwo, map_neg, coefficient_fOne_zero, coefficient_fTwo_zero]
    linear_combination -2 * seed_mixed_sum
  · simp only [map_add, map_smul, smul_eq_mul, A_coeff_one, B_coeff_one, mul_zero, mul_one, add_zero]
    simp only [B, map_add, map_smul, smul_eq_mul, diamond_two_fOne,
      diamond_two_fTwo, map_neg, coefficient_fOne_one, coefficient_fTwo_one]
    linear_combination -2 * seed_first_square_sum

end ZInQ.Contrib.HeckePrimeRationality.NormalizedFive
