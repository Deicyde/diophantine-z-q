import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model
import ZInQKernel.Contrib.OneProof.RC.CMField2.HeegnerLattice

/-! A collision of the two plane coordinates on the normalized level-two curve.
On-the-spot calculation (c), for the branch comparison at tex 2915–2916. -/

noncomputable section

open UpperHalfPlane Complex Matrix
open scoped MatrixGroups
open ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.CMField2

local notation "τ₊" => cmPoint 2 1 (-7)
local notation "τ₋" => cmPoint 2 (-1) (-7)

theorem levelTwo_heegner :
    IsHeegnerForm 2 (-7) 2 1 1 ∧ IsHeegnerForm 2 (-7) 2 (-1) 1 ∧
      IsCoprime (-7 : ℤ) 2 := by
  refine ⟨by unfold IsHeegnerForm; decide, by unfold IsHeegnerForm; decide, -1, -3, by norm_num⟩

private abbrev s : ℝ := Real.sqrt 7

private theorem hs : s ^ 2 = 7 := Real.sq_sqrt (by norm_num)

private theorem hplus : (τ₊ : ℂ) = (-1 + Complex.I * (s : ℂ)) / 4 := by
  rw [coe_cmPoint_of_neg (by decide) (by decide)]
  norm_num

private theorem hminus : (τ₋ : ℂ) = (1 + Complex.I * (s : ℂ)) / 4 := by
  rw [coe_cmPoint_of_neg (by decide) (by decide)]
  norm_num

private theorem hshift : (τ₋ : ℂ) = (τ₊ : ℂ) + 1 / 2 := by
  rw [hplus, hminus]
  ring

private theorem hquad : (τ₊ : ℂ) ^ 2 = -(τ₊ : ℂ) / 2 - 1 / 2 := by
  have hsq : (s : ℂ)^2 = 7 := by exact_mod_cast hs
  rw [hplus]
  linear_combination ((s : ℂ)^2 / 16) * Complex.I_sq - (1 / 16 : ℂ) * hsq

private theorem hprod : (τ₊ : ℂ) * (τ₋ : ℂ) = -1 / 2 := by
  rw [hshift, mul_add, ← pow_two, hquad]
  ring

/-- Reflection in the imaginary axis interchanges the two parameters. -/
theorem levelTwo_reflection : -(star (τ₊ : ℂ)) = (τ₋ : ℂ) := by
  rw [hplus, hminus]
  change -(starRingEnd ℂ ((-1 + Complex.I * (s : ℂ)) / 4)) = _
  simp only [map_div₀, map_add, map_mul, map_neg, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

private theorem S_plus : ModularGroup.S • τ₊ = X0Model.dilate 2 τ₋ := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.modular_S_smul]
  change (-(τ₊ : ℂ))⁻¹ = 2 * (τ₋ : ℂ)
  rw [← one_div, div_eq_iff (neg_ne_zero.mpr τ₊.ne_zero)]
  linear_combination 2 * hprod

private theorem S_minus : ModularGroup.S • τ₋ = X0Model.dilate 2 τ₊ := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.modular_S_smul]
  change (-(τ₋ : ℂ))⁻¹ = 2 * (τ₊ : ℂ)
  rw [← one_div, div_eq_iff (neg_ne_zero.mpr τ₋.ne_zero)]
  linear_combination 2 * hprod

private theorem T_dilate : ModularGroup.T • X0Model.dilate 2 τ₊ = X0Model.dilate 2 τ₋ := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
  change (1 : ℂ) + 2 * (τ₊ : ℂ) = 2 * (τ₋ : ℂ)
  rw [hshift]
  ring

/-- Both plane j-coordinates agree. -/
theorem levelTwo_coordinates : X0Model.analyticJ τ₊ = X0Model.analyticJ τ₋ ∧
    X0Model.analyticJN 2 τ₊ = X0Model.analyticJN 2 τ₋ := by
  have h := (X0Model2.analyticJ_eq_iff _ _).mpr ⟨ModularGroup.T, T_dilate⟩
  exact ⟨((X0Model2.analyticJ_eq_iff _ _).mpr ⟨ModularGroup.S, S_plus⟩).trans
    (h.symm.trans ((X0Model2.analyticJ_eq_iff _ _).mpr ⟨ModularGroup.S, S_minus⟩).symm), h⟩

/-- At level two the middle coefficient of a form of even leading coefficient
is unchanged modulo four by the substitution given by a matrix in Γ₀(2). -/
theorem middleCoefficient_mod_four {A B C p q r s : ℤ}
    (hA : 2 ∣ A) (hr : 2 ∣ r) (hdet : p * s - q * r = 1) :
    (4 : ℤ) ∣ (2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s) - B := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨c, rfl⟩ := hr
  refine ⟨a * p * q + B * q * c + C * c * s, ?_⟩
  linear_combination B * hdet

/-- The Γ₀(2) orbits are distinct. For this example the middle-coefficient obstruction
can be checked directly: any such matrix would have a=d and 2b=d-c. -/
theorem levelTwo_distinct :
    (X0Branch.model 2).complexPoint τ₊ ≠ (X0Branch.model 2).complexPoint τ₋ := by
  intro he
  obtain ⟨γ, hγ, ht⟩ := ((X0Branch.model 2).complexPoint_eq_iff _ _).mp he
  have hc := CongruenceSubgroup.Gamma0_mem.mp hγ
  have hd : (γ 1 0 : ℂ) * (τ₊ : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
    exact UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ₊
  have hm := congrArg (fun z : ℍ => (z : ℂ)) ht
  rw [X0Model2.coe_sl_smul, X0Model2.slMoebius, div_eq_iff hd] at hm
  have hlin : ((γ 0 0 : ℂ) - (γ 1 1 : ℂ)) * (τ₊ : ℂ) +
      ((γ 0 1 : ℂ) - ((γ 1 1 : ℂ) - (γ 1 0 : ℂ)) / 2) = 0 := by
    rw [hshift] at hm
    linear_combination hm + (γ 1 0 : ℂ) * hquad
  have hlin2 : (2 * ((γ 0 0 : ℂ) - (γ 1 1 : ℂ))) * (τ₊ : ℂ) +
      (2 * (γ 0 1 : ℂ) - (γ 1 1 : ℂ) + (γ 1 0 : ℂ)) = 0 := by
    linear_combination 2 * hlin
  have hi := congrArg Complex.im hlin2
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.intCast_im,
    sub_self, zero_mul, mul_zero, add_zero, sub_zero, Complex.sub_re, Complex.intCast_re,
    Complex.zero_im, show (2 : ℂ).im = 0 by rfl, show (2 : ℂ).re = 2 by rfl] at hi
  have haR : (γ 0 0 : ℝ) = (γ 1 1 : ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hi).resolve_right τ₊.im_pos.ne')).resolve_left
      (by norm_num))
  have ha : γ 0 0 = γ 1 1 := by exact_mod_cast haR
  rw [ha, sub_self, zero_mul, zero_add, sub_eq_zero] at hlin
  have hb := congrArg (fun z : ℂ => 2 * z) hlin
  have hb' : (2 : ℂ) * (γ 0 1 : ℂ) = (γ 1 1 : ℂ) - (γ 1 0 : ℂ) := by
    linear_combination hb
  have hbZ : 2 * γ 0 1 = γ 1 1 - γ 1 0 := by exact_mod_cast hb'
  have hc' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
  have he : (2 : ℤ) ∣ γ 1 1 := by
    have h : γ 1 1 = 2 * γ 0 1 + γ 1 0 := by omega
    rw [h]
    exact dvd_add (dvd_mul_right _ _) hc'
  have hdet := γ.property
  rw [Matrix.det_fin_two] at hdet
  have hdiv : (2 : ℤ) ∣ γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 :=
    dvd_sub (he.mul_left _) (hc'.mul_left _)
  rw [hdet] at hdiv
  norm_num at hdiv


end ZInQ.Manuscript.RC.CMField2
