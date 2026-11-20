import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.Tactic

/-! The classical fourth-power transformation, from the two Jacobi
formulas and Euclidean reduction in Gamma0(4). -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open Complex CongruenceSubgroup Matrix Matrix.SpecialLinearGroup ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups

private abbrev theta (z : ℍ) : ℂ := jacobiTheta (2 * (z : ℂ))

private def lower (n : ℤ) : SL(2, ℤ) := ⟨!![1, 0; 4 * n, 1], by simp [det_fin_two]⟩

private theorem lower_add (m n : ℤ) : lower (m + n) = lower m * lower n := by
  apply Subtype.ext
  rw [coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lower, Matrix.mul_apply, Fin.sum_univ_two, mul_add]

private theorem transform_characterization (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[(2 : ℤ)] γ = f ↔
      ∀ z : ℍ, f (γ • z) = ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) ^ 2 * f z := by
  rw [funext_iff]
  exact forall_congr' fun z => by
    simpa only [zpow_ofNat] using slash_action_eq'_iff 2 f γ z

private def thetaStabilizer : Subgroup SL(2, ℤ) where
  carrier := {γ | (fun z => theta z ^ 4) ∣[(2 : ℤ)] γ = (fun z => theta z ^ 4)}
  one_mem' := SlashAction.slash_one _ _
  mul_mem' := by
    intro a b ha hb
    change _ ∣[(2 : ℤ)] (a * b) = _
    rw [SlashAction.slash_mul, ha, hb]
  inv_mem' := by
    intro a ha
    have e := congrArg (fun (f : ℍ → ℂ) => f ∣[(2 : ℤ)] a⁻¹) ha
    change (fun z => theta z ^ 4) ∣[(2 : ℤ)] a⁻¹ = (fun z => theta z ^ 4)
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] using e.symm

private theorem mem_thetaStabilizer (γ : SL(2, ℤ)) :
    γ ∈ thetaStabilizer ↔ ∀ z : ℍ,
      theta (γ • z) ^ 4 = ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) ^ 2 * theta z ^ 4 :=
  transform_characterization _ γ

private theorem T_mem_stabilizer : ModularGroup.T ∈ thetaStabilizer := by
  apply (mem_thetaStabilizer _).2
  intro z
  simp only [modular_T_smul, theta, coe_vadd, Complex.ofReal_one]
  have ht : (2 : ℂ) * (1 + (z : ℂ)) = 2 + 2 * (z : ℂ) := by ring
  rw [ht, jacobiTheta_two_add]
  simp [ModularGroup.T]

private theorem neg_one_mem_stabilizer : (-1 : SL(2, ℤ)) ∈ thetaStabilizer := by
  apply (mem_thetaStabilizer _).2
  intro z
  rw [show (-1 : SL(2, ℤ)) • z = z from
    (ModularGroup.SL_neg_smul 1 z).trans (one_smul _ _)]
  simp

private theorem jacobiTheta_fricke_fourth {z : ℂ} (hz : 0 < z.im) :
    jacobiTheta (2 * (-1 / (4 * z))) ^ 4 = -4 * z ^ 2 * jacobiTheta (2 * z) ^ 4 := by
  have hz0 : z ≠ 0 := fun hz0 => by simp [hz0] at hz
  let w : ℍ := ⟨2 * z, by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hz⟩
  have hd : (↑(ModularGroup.S • w) : ℂ) = 2 * (-1 / (4 * z)) := by
    rw [modular_S_smul]
    change (-(2 * z))⁻¹ = _
    field_simp
    norm_num
  have e := jacobiTheta_S_smul w
  rw [hd] at e
  change jacobiTheta (2 * (-1 / (4 * z))) =
    (-Complex.I * (2 * z)) ^ (1 / 2 : ℂ) * jacobiTheta (2 * z) at e
  rw [e, mul_pow, ← Complex.cpow_mul_nat,
    show (1 / 2 : ℂ) * (4 : ℕ) = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  congr 1
  rw [mul_pow, neg_sq, Complex.I_sq]
  ring

private theorem lower_one_mem_stabilizer : lower 1 ∈ thetaStabilizer := by
  apply (mem_thetaStabilizer _).2
  intro z
  let v : ℂ := -1 / (4 * (z : ℂ))
  let w : ℂ := v - 1
  have hz : (z : ℂ) ≠ 0 := by
    intro e
    have h : 0 < (z : ℂ).im := z.im_pos
    rw [e, zero_im] at h
    exact (lt_irrefl 0) h
  have hv : 0 < v.im := by
    have ht : 0 < ((4 : ℂ) * (z : ℂ)).im := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 4) z.im_pos
    have hn : (4 : ℂ) * (z : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hz
    dsimp [v]
    rw [neg_div, neg_im, one_div, inv_im, neg_div, neg_neg]
    exact div_pos ht (normSq_pos.mpr hn)
  have hw : 0 < w.im := by simpa [w] using hv
  have hw0 : w ≠ 0 := fun e => by simp [e] at hw
  have hd : 4 * (z : ℂ) + 1 ≠ 0 := by
    intro e
    have hpos : 0 < ((4 : ℂ) * (z : ℂ) + 1).im := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 4) z.im_pos
    rw [e, zero_im] at hpos
    exact (lt_irrefl 0) hpos
  have harg : ((lower 1 • z : ℍ) : ℂ) = -1 / (4 * w) := by
    rw [coe_specialLinearGroup_apply]
    simp [lower]
    have he : 4 * w = -(4 * (z : ℂ) + 1) / (z : ℂ) := by
      dsimp [w, v]
      field_simp
      ring
    rw [he, div_div_eq_mul_div]
    have ee : (-1 : ℂ) * (z : ℂ) = -(z : ℂ) := by ring
    rw [ee, neg_div_neg_eq]
  have hp : jacobiTheta (2 * w) = jacobiTheta (2 * v) := by
    rw [← jacobiTheta_two_add (2 * w), show (2 : ℂ) + 2 * w = 2 * v by dsimp [w]; ring]
  rw [show theta (lower 1 • z) = jacobiTheta (2 * (-1 / (4 * w))) by
    unfold theta; rw [harg]]
  have h10 : (lower 1) 1 0 = 4 := by simp [lower]
  have h11 : (lower 1) 1 1 = 1 := by simp [lower]
  simp only [theta, h10, h11, Int.cast_ofNat, Int.cast_one]
  rw [jacobiTheta_fricke_fourth hw, hp]
  change -4 * w ^ 2 * jacobiTheta (2 * (-1 / (4 * (z : ℂ)))) ^ 4 = _
  rw [jacobiTheta_fricke_fourth z.im_pos]
  dsimp [w, v]
  field_simp
  ring

private theorem lower_mem_stabilizer (n : ℤ) : lower n ∈ thetaStabilizer := by
  let lowerHom : Multiplicative ℤ →* SL(2, ℤ) :=
    { toFun := fun a => lower a.toAdd
      map_one' := by decide
      map_mul' := fun m n => lower_add m.toAdd n.toAdd }
  have hpow : lower n = (lower 1) ^ n := by
    have h := map_zpow lowerHom (Multiplicative.ofAdd (1 : ℤ)) n
    change lower ((Multiplicative.ofAdd (1 : ℤ) ^ n).toAdd) = (lower 1) ^ n at h
    simpa using h
  rw [hpow]
  exact thetaStabilizer.zpow_mem lower_one_mem_stabilizer n

private theorem triangular_mem {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) : γ ∈ thetaStabilizer := by
  have hdet := γ.det_coe
  rw [det_fin_two, hc, mul_zero, sub_zero] at hdet
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
    Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ (mul_comm _ _ |>.trans hdet))
  rcases hd with hd | hd
  · have ha : γ 0 0 = 1 := by simpa [hd] using hdet
    have he : γ = ModularGroup.T ^ (γ 0 1) := by
      apply Subtype.ext
      rw [ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    rw [he]
    exact thetaStabilizer.zpow_mem T_mem_stabilizer _
  · have ha : γ 0 0 = -1 := by rw [hd] at hdet; linarith
    have he : γ = -1 * ModularGroup.T ^ (-(γ 0 1)) := by
      apply Subtype.ext
      rw [coe_mul, show ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = -1 from rfl,
        neg_mul, one_mul, ModularGroup.coe_T_zpow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hc, hd]
    rw [he]
    exact thetaStabilizer.mul_mem neg_one_mem_stabilizer
      (thetaStabilizer.zpow_mem T_mem_stabilizer _)

/-- Centre a residue using the two consecutive Euclidean representatives. -/
private theorem centre (a b : ℤ) (hb : b ≠ 0) :
    ∃ t : ℤ, 2 * (a + t * b).natAbs ≤ b.natAbs := by
  have hb0 : (0 : ℤ) < b.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hb
  have hr0 := Int.emod_nonneg a hb
  have hrb := Int.emod_lt_abs a hb
  rw [Int.abs_eq_natAbs] at hrb
  have hab := Int.emod_add_mul_ediv a b
  by_cases h : 2 * (a % b) ≤ b.natAbs
  · refine ⟨-(a / b), ?_⟩
    have he : a + -(a / b) * b = a % b := by linear_combination hab.symm
    rw [he]
    omega
  · rcases le_or_gt 0 b with hb' | hb'
    · refine ⟨-(a / b) - 1, ?_⟩
      have he : a + (-(a / b) - 1) * b = a % b - b := by linear_combination hab.symm
      rw [he]
      have hba := Int.natAbs_of_nonneg hb'
      rw [hba] at hrb h
      have hbr : a % b - b ≤ 0 := by omega
      exact_mod_cast (show 2 * (↑(a % b - b).natAbs : ℤ) ≤ (b.natAbs : ℤ) by
        rw [Int.ofNat_natAbs_of_nonpos hbr, hba]
        omega)
    · refine ⟨-(a / b) + 1, ?_⟩
      have he : a + (-(a / b) + 1) * b = a % b + b := by linear_combination hab.symm
      rw [he]
      have hba := Int.ofNat_natAbs_of_nonpos hb'.le
      rw [hba] at hrb h
      have hbr : a % b + b ≤ 0 := by omega
      exact_mod_cast (show 2 * (↑(a % b + b).natAbs : ℤ) ≤ (b.natAbs : ℤ) by
        rw [Int.ofNat_natAbs_of_nonpos hbr, hba]
        omega)

private theorem Tmul_entries (n : ℤ) (γ : SL(2, ℤ)) :
    (ModularGroup.T ^ n * γ) 0 0 = γ 0 0 + n * γ 1 0 ∧
    (ModularGroup.T ^ n * γ) 1 0 = γ 1 0 := by
  simp only [coe_mul, ModularGroup.coe_T_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem lowerMul_entry (n : ℤ) (γ : SL(2, ℤ)) :
    (lower n * γ) 1 0 = 4 * n * γ 0 0 + γ 1 0 := by
  rw [show (lower n * γ).val = (lower n).val * γ.val from rfl]
  simp [lower, Matrix.mul_apply, Fin.sum_univ_two]

private theorem stabilizer_of_c (k : ℤ) (γ : SL(2, ℤ)) (hc : γ 1 0 = 4 * k) :
    γ ∈ thetaStabilizer := by
  induction hn : k.natAbs using Nat.strong_induction_on generalizing k γ with
  | h n ih =>
    by_cases hk : k = 0
    · exact triangular_mem (by simp [hc, hk])
    have hc0 : γ 1 0 ≠ 0 := by simp [hc, hk]
    obtain ⟨t, ht⟩ := centre (γ 0 0) (γ 1 0) hc0
    let γ' := ModularGroup.T ^ t * γ
    have he := Tmul_entries t γ
    have hc' : γ' 1 0 = 4 * k := he.2.trans hc
    have ht' : 2 * (γ' 0 0).natAbs ≤ 4 * k.natAbs := by
      simpa only [γ', he.1, hc, Int.natAbs_mul, show (4 : ℤ).natAbs = 4 from rfl] using ht
    have hdet := γ'.det_coe
    rw [det_fin_two, hc'] at hdet
    have haodd : γ' 0 0 % 2 = 1 := by
      by_contra h
      have he : γ' 0 0 = 2 * (γ' 0 0 / 2) := by omega
      rw [he] at hdet
      have hdiv : (2 : ℤ) ∣ 1 := by
        refine ⟨(γ' 0 0 / 2) * γ' 1 1 - 2 * k * γ' 0 1, ?_⟩
        linear_combination -hdet
      norm_num at hdiv
    have ha : γ' 0 0 ≠ 0 := by intro e; simp [e] at haodd
    have hlt : (γ' 0 0).natAbs < 2 * k.natAbs := by omega
    obtain ⟨l, hl⟩ := centre k (γ' 0 0) ha
    have hcl : (lower l * γ') 1 0 = 4 * (k + l * γ' 0 0) := by
      rw [lowerMul_entry, hc']
      ring
    have hnew := ih (k + l * γ' 0 0).natAbs (by omega) _ _ hcl rfl
    have hγ' : γ' ∈ thetaStabilizer := by
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using
        thetaStabilizer.mul_mem (thetaStabilizer.inv_mem (lower_mem_stabilizer l)) hnew
    simpa only [γ', ← mul_assoc, inv_mul_cancel, one_mul] using
      thetaStabilizer.mul_mem (thetaStabilizer.inv_mem
        (thetaStabilizer.zpow_mem T_mem_stabilizer t)) hγ'

/-- The fourth power of the ordinary Jacobi theta series has the weight-two
transformation on Gamma0(4). -/
theorem jacobiTheta_fourth_transform (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 4) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) ^ 4 =
      ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) ^ 2 * jacobiTheta (2 * (z : ℂ)) ^ 4 := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (Gamma0_mem.mp hγ)
  exact (mem_thetaStabilizer γ).mp (stabilizer_of_c k γ hk) z


end ZInQ.Manuscript.RC.EvenExpansion
