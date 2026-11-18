import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelIntegerRows
import WeightTwoConstants04

/-!
# A genuine torsion separator for the Gamma-one quotient

For level at least three, the completed torsion logarithmic derivative
at the row (0,1) has stabilizer exactly Gamma-one in the integral modular
group. The proof compares actual principal-period constant coefficients:
non-axis constants are real, whereas the primitive axis constant is
nonzero and purely imaginary. The axis fractional-linear expression
then recovers its residue label.

This is a separating-orbit result, not a spanning theorem for cusp forms.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace DirectTorsionSeparator

open ZInQ.Contrib.HeckePrimeRationality
open Torsion AllLevelForms

/-- The fractional-linear expression appearing in the actual axis constant. -/
def axisMobius (v : ℂ) : ℂ := (v + 1) / (2 * (v - 1))

/-- This axis expression distinguishes any two admissible roots. -/
theorem axisMobius_injective {v w : ℂ} (hv : v ≠ 1) (hw : w ≠ 1)
    (h : axisMobius v = axisMobius w) : v = w := by
  unfold axisMobius at h
  have hv' : v - 1 ≠ 0 := sub_ne_zero.mpr hv
  have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  field_simp [hv', hw'] at h
  linear_combination -h / 2

/-- On the unit circle the axis expression is purely imaginary. -/
theorem axisMobius_conj_neg {v : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hvnorm : ‖v‖ = 1) : starRingEnd ℂ (axisMobius v) = -axisMobius v := by
  have hconj : starRingEnd ℂ v = v⁻¹ := (Complex.inv_eq_conj hvnorm).symm
  have hv' : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
  have hi : v⁻¹ - 1 ≠ 0 := by
    intro h
    have hinv : v⁻¹ = 1 := sub_eq_zero.mp h
    exact hv1 (by simpa using congrArg Inv.inv hinv)
  simp only [axisMobius, map_div₀, map_add, map_mul, map_sub, map_one, map_ofNat, hconj]
  field_simp [hv0, hv', hi]
  ring

/-- A primitive root of order at least three gives an axis constant not fixed by conjugation. -/
theorem axisMobius_not_conj_fixed {v : ℂ} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (hvm : v ≠ -1) (hvnorm : ‖v‖ = 1) :
    starRingEnd ℂ (axisMobius v) ≠ axisMobius v := by
  intro h
  have hn := axisMobius_conj_neg hv0 hv1 hvnorm
  rw [h] at hn
  have hz : axisMobius v = 0 := by linear_combination hn / 2
  have hd : 2 * (v - 1) ≠ 0 := mul_ne_zero two_ne_zero (sub_ne_zero.mpr hv1)
  have hnum : v + 1 = 0 := (div_eq_zero_iff.mp hz).resolve_right hd
  exact hvm (by linear_combination hnum)

variable (N : ℕ) [NeZero N]

/-- The actual period-N constant on every normalized good torsion row. -/
theorem torsion_coeff_zero_normalized (a : ℕ) (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    (qExpansion (N : ℝ) (torsionLogDerivative N a b)).coeff 0 =
      if a = 0 then axisMobius (w N b) else (a : ℂ) / (N : ℂ) - 1 / 2 := by
  rw [AllLevelPrincipalCoefficients.torsion_qExpansion N a ha b hg,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hP : PowerSeries.constantCoeff (AllLevelPrincipalCoefficients.P N a (w N b)) =
      if a = 0 then 1 - (w N b)⁻¹ else -(w N b)⁻¹ := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      AllLevelPrincipalCoefficients.P_zero (NeZero.pos N) ha]
  have hM : PowerSeries.constantCoeff (AllLevelPrincipalCoefficients.M N a (w N b)) =
      (w N b)⁻¹ := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact WeightTwoConstants.firstSeries_zero (NeZero.pos N) ha (w N b)
  simp only [AllLevelPrincipalCoefficients.R, map_add, map_mul, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_inv, hP, hM, AllLevelPrincipalCoefficients.completion]
  have hv0 := AllLevelTorsionCoefficients.w_ne_zero N b
  by_cases hz : a = 0
  · subst a
    have hb : ¬ (N : ℤ) ∣ b := by simpa using hg
    have hv1 : w N b ≠ 1 := fun h => hb ((AllLevelTorsionCoefficients.w_eq_one_iff N b).mp h)
    have hd : w N b - 1 ≠ 0 := sub_ne_zero.mpr hv1
    have hi : 1 - (w N b)⁻¹ ≠ 0 := by
      intro h
      have hinv : (w N b)⁻¹ = 1 := by linear_combination -h
      exact hv1 (by simpa using congrArg Inv.inv hinv)
    simp only [↓reduceIte, Nat.cast_zero, zero_div, zero_add, axisMobius]
    field_simp [hv0, hd, hi]
    ring
  · simp only [if_neg hz]
    field_simp [hv0]
    ring

/-- The actual primitive axis root is neither one nor minus one at these levels. -/
theorem primitive_axis_not_sign (hN : 3 ≤ N) : w N 1 ≠ 1 ∧ w N 1 ≠ -1 := by
  have hdiv1 : ¬ (N : ℤ) ∣ 1 := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) (by omega : 1 < N))
  have hdiv2 : ¬ (N : ℤ) ∣ 2 := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < N))
  refine ⟨fun h => hdiv1 ((AllLevelTorsionCoefficients.w_eq_one_iff N 1).mp h), ?_⟩
  intro hm
  have hzeta : zeta N = -1 := by simpa only [w, zpow_one] using hm
  have h2 : w N 2 = 1 := by simp [w, hzeta]
  exact hdiv2 ((AllLevelTorsionCoefficients.w_eq_one_iff N 2).mp h2)

/-- The completed torsion function at (0,1) has no larger integral stabilizer
than the actual Gamma-one subgroup, for every level at least three. -/
theorem torsion_slash_eq_self_iff (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    (F N (0, 1) ∣[(1 : ℤ)] γ = F N (0, 1)) ↔ γ ∈ Gamma1 N := by
  have hdiv1 : ¬ (N : ℤ) ∣ 1 := by
    exact_mod_cast (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) (by omega : 1 < N))
  have hbase : Good N (0, 1) := fun h => hdiv1 h.2
  constructor
  · intro hfix
    have hact : ThetaFiveTorsion.act (0, 1) γ = (γ 1 0, γ 1 1) := by
      simp [ThetaFiveTorsion.act]
    have hgood : ¬ ((N : ℤ) ∣ γ 1 0 ∧ (N : ℤ) ∣ γ 1 1) := by
      simpa only [hact, Good] using good_act hbase γ
    have he : torsionLogDerivative N (γ 1 0) (γ 1 1) = torsionLogDerivative N 0 1 := by
      have hs := F_slash (NeZero.pos N) γ (0, 1) hbase
      rw [hact, hfix] at hs
      exact hs.symm
    let A : ℤ := γ 1 0 % (N : ℤ)
    have hA0 : 0 ≤ A := Int.emod_nonneg _ (by exact_mod_cast NeZero.ne N)
    have hAN : A < (N : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos N)
    have hcast : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
    have ha : A.toNat < N := by omega
    have hgoodA : ¬ ((N : ℤ) ∣ (A.toNat : ℤ) ∧ (N : ℤ) ∣ γ 1 1) := by
      rw [hcast]
      exact AllLevelIntegerRows.normal_good N (γ 1 0) (γ 1 1) hgood
    have heA : torsionLogDerivative N A.toNat (γ 1 1) = torsionLogDerivative N 0 1 := by
      rw [hcast]
      exact (AllLevelIntegerRows.torsion_eq_normal N (γ 1 0) (γ 1 1) hgood).symm.trans he
    have hc := congrArg (fun f : ℍ → ℂ => (qExpansion (N : ℝ) f).coeff 0) heA
    have hzeroBase : (qExpansion (N : ℝ) (torsionLogDerivative N 0 1)).coeff 0 =
        axisMobius (w N 1) := by
      simpa only [Nat.cast_zero, ↓reduceIte] using
        torsion_coeff_zero_normalized N 0 (NeZero.pos N) 1 hbase
    rw [torsion_coeff_zero_normalized N A.toNat ha (γ 1 1) hgoodA, hzeroBase] at hc
    have hAzero : A.toNat = 0 := by
      by_contra hAzero
      simp only [if_neg hAzero, if_pos rfl] at hc
      have hreal : starRingEnd ℂ (axisMobius (w N 1)) = axisMobius (w N 1) := by
        rw [← hc]
        simp [map_ofNat]
      exact axisMobius_not_conj_fixed (AllLevelTorsionCoefficients.w_ne_zero N 1)
        (primitive_axis_not_sign N hN).1 (primitive_axis_not_sign N hN).2
        (AllLevelTorsionCoefficients.norm_w N 1) hreal
    have hAeq : A = 0 := by omega
    have hbottom : (N : ℤ) ∣ γ 1 0 := by
      refine ⟨γ 1 0 / (N : ℤ), ?_⟩
      have h := Int.emod_add_mul_ediv (γ 1 0) (N : ℤ)
      change A + (N : ℤ) * (γ 1 0 / (N : ℤ)) = γ 1 0 at h
      simpa only [hAeq, zero_add] using h.symm
    have hgoodD : ¬ (N : ℤ) ∣ γ 1 1 := fun h => hgood ⟨hbottom, h⟩
    simp only [if_pos hAzero, if_pos rfl] at hc
    have hwd : w N (γ 1 1) = w N 1 := axisMobius_injective
      (fun h => hgoodD ((AllLevelTorsionCoefficients.w_eq_one_iff N _).mp h))
      (primitive_axis_not_sign N hN).1 hc
    have hdroot : w N (γ 1 1 - 1) = 1 := by
      rw [w, zpow_sub₀ (show zeta N ≠ 0 from Complex.exp_ne_zero _)]
      change w N (γ 1 1) / w N 1 = 1
      rw [hwd, div_self (AllLevelTorsionCoefficients.w_ne_zero N 1)]
    have hdivD : (N : ℤ) ∣ γ 1 1 - 1 :=
      (AllLevelTorsionCoefficients.w_eq_one_iff N _).mp hdroot
    have hcZ : (γ 1 0 : ZMod N) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hbottom
    have hdZ : (γ 1 1 : ZMod N) = 1 := by
      have h := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 1 1) N).mpr hdivD
      simpa using h.symm
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      simpa only [Matrix.det_fin_two] using γ.property
    have hdetZ : (γ 0 0 : ZMod N) * (γ 1 1 : ZMod N) -
        (γ 0 1 : ZMod N) * (γ 1 0 : ZMod N) = 1 := by
      simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using
        congrArg (fun z : ℤ => (z : ZMod N)) hdet
    have haZ : (γ 0 0 : ZMod N) = 1 := by simpa only [hcZ, hdZ, mul_one, mul_zero, sub_zero] using hdetZ
    exact (Gamma1_mem N γ).mpr ⟨haZ, hdZ, hcZ⟩
  · intro hγ
    exact F_slash_Gamma1 (NeZero.pos N) hdiv1 γ hγ

/-- Distinct actual Gamma-one cosets give distinct torsion translates. -/
theorem torsion_slash_eq_iff (hN : 3 ≤ N) (γ δ : SL(2, ℤ)) :
    F N (0, 1) ∣[(1 : ℤ)] γ = F N (0, 1) ∣[(1 : ℤ)] δ ↔ γ * δ⁻¹ ∈ Gamma1 N := by
  constructor
  · intro h
    apply (torsion_slash_eq_self_iff N hN (γ * δ⁻¹)).mp
    rw [SlashAction.slash_mul, h, ← SlashAction.slash_mul,
      mul_inv_cancel, SlashAction.slash_one]
  · intro h
    have hs := (torsion_slash_eq_self_iff N hN (γ * δ⁻¹)).mpr h
    have he : γ = (γ * δ⁻¹) * δ := by group
    rw [he, SlashAction.slash_mul, hs]

end DirectTorsionSeparator
