import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Cusps
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Fourier
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaNonvanishing
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.ThetaPoisson

/-!
# The theta ratio under translation conjugates

Only the comparison needed by tex 8101–8103 is asserted here. The proof
uses the unevaluated quadratic sum in the Poisson expansion, so no
quadratic reciprocity formula or square-root sign comparison is needed
(provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Real

private abbrev θ (z : ℍ) : ℂ := jacobiTheta (2 * (z : ℂ))

private abbrev J (γ : SL(2, ℤ)) (z : ℍ) : ℂ := θ (γ • z) / θ z

private theorem theta_pos_im (z : ℍ) : 0 < (2 * (z : ℂ)).im := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
  exact mul_pos (by norm_num) z.im_pos

private theorem coe_sl_smul (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℤ) * (z : ℂ) + (γ 0 1 : ℤ)) /
      ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply γ z]
  simp

private theorem J_of_c_zero {γ : SL(2, ℤ)} (hc : γ 1 0 = 0) (z : ℍ) : J γ z = 1 := by
  have hdet : γ 0 0 * γ 1 1 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    simpa [hc] using h
  have hd : γ 1 1 = 1 ∨ γ 1 1 = -1 :=
    Int.isUnit_iff.mp (show IsUnit (γ 1 1) from
      (Units.mkOfMulEqOne _ _ (by simpa only [mul_comm] using hdet)).isUnit)
  have he : ((γ • z : ℍ) : ℂ) = (z : ℂ) + ((γ 0 1 * γ 1 1 : ℤ) : ℂ) := by
    rw [coe_sl_smul]
    rcases hd with h | h
    · have ha : γ 0 0 = 1 := by simpa [h] using hdet
      simp [h, ha, hc]
    · have ha : γ 0 0 = -1 := by rw [h] at hdet; omega
      simp [h, ha, hc]
      ring
  have hper : Function.Periodic (fun z : ℂ ↦ jacobiTheta (2 * z)) 1 := by
    intro x
    change jacobiTheta (2 * (x + 1)) = jacobiTheta (2 * x)
    rw [show (2 : ℂ) * (x + 1) = 2 + 2*x by ring, jacobiTheta_two_add]
  unfold J θ
  rw [he]
  have h := (hper.int_mul (γ 0 1 * γ 1 1)) (z : ℂ)
  change jacobiTheta (2 * ((z : ℂ) + ((γ 0 1 * γ 1 1 : ℤ) : ℂ) * 1)) = _ at h
  rw [mul_one] at h
  rw [h, div_self (jacobiTheta_ne_zero_of_im_pos (theta_pos_im z))]

private theorem J_at_cusp (γ : SL(2, ℤ)) {k : ℕ} [NeZero (4 * k)]
    (hc : γ 1 0 = ((4 * k : ℕ) : ℤ)) (z : ℍ) :
    let C := (4 * k : ℕ)
    let t := (z : ℂ) / 2 + ((γ 1 1 : ℤ) : ℂ) / (2 * C)
    J γ z = (1 / (-Complex.I * (-1 / t)) ^ (1 / 2 : ℂ)) *
      quadraticFourier ((γ 0 0 : ℤ) : ZMod C) 0 := by
  let C := 4 * k
  let a := γ 0 0
  let b := γ 0 1
  let d := γ 1 1
  have hdet : a * d - b * (C : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two, hc] at h
    exact h
  have had : (a : ZMod C) * d = 1 := by
    simpa [Int.cast_sub, Int.cast_mul] using congrArg (Int.cast : ℤ → ZMod C) hdet
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have hd : (C : ℂ) * (z : ℂ) + (d : ℂ) ≠ 0 := by
    intro h
    have h' := congrArg Complex.im h
    have hh : 0 < (C : ℝ) * (z : ℂ).im :=
      mul_pos (Nat.cast_pos.mpr (NeZero.pos C)) z.im_pos
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_intCast, Complex.add_im,
      Complex.im_ofReal_mul, Complex.ofReal_im, Complex.zero_im, add_zero] at h'
    exact hh.ne' h'
  have hd' : (z : ℂ) * (C : ℂ) + (d : ℂ) ≠ 0 := by
    simpa only [mul_comm] using hd
  have he : 2 * ((γ • z : ℍ) : ℂ) =
      2 * (a : ℂ) / C - 2 / ((C : ℂ) * ((C : ℂ) * (z : ℂ) + (d : ℂ))) := by
    rw [coe_sl_smul, hc]
    simp only [Int.cast_natCast]
    change 2 * (((a : ℂ) * (z : ℂ) + b) / ((C : ℂ) * (z : ℂ) + d)) = _
    have h := congrArg (Int.cast : ℤ → ℂ) hdet
    push_cast at h
    field_simp [hC, hd, hd']
    linear_combination -h
  change θ (γ • z) / θ z = _
  unfold θ
  rw [he, jacobiTheta_at_cusp a d z.im_pos had, mul_div_cancel_right₀ _
    (jacobiTheta_ne_zero_of_im_pos (theta_pos_im z))]

private theorem conjugate_entries (t s : ℚ) (γ δ : SL(2, ℤ))
    (he : translateMatrix t * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix s) :
    δ 1 0 = γ 1 0 ∧
      ((δ 0 0 : ℤ) : ℚ) = (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ) ∧
      ((δ 1 1 : ℤ) : ℚ) + (δ 1 0 : ℤ) * s = (γ 1 1 : ℤ) := by
  have h (i j : Fin 2) := congrArg (fun g : SL(2, ℚ) ↦ g i j) he
  have h10 := h 1 0
  have h00 := h 0 0
  have h11 := h 1 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at h10 h00 h11
  change 0 * ((γ 0 0 : ℤ) : ℚ) + 1 * ((γ 1 0 : ℤ) : ℚ) =
      ((δ 1 0 : ℤ) : ℚ) * 1 + ((δ 1 1 : ℤ) : ℚ) * 0 at h10
  change 1 * ((γ 0 0 : ℤ) : ℚ) + t * ((γ 1 0 : ℤ) : ℚ) =
      ((δ 0 0 : ℤ) : ℚ) * 1 + ((δ 0 1 : ℤ) : ℚ) * 0 at h00
  change 0 * ((γ 0 1 : ℤ) : ℚ) + 1 * ((γ 1 1 : ℤ) : ℚ) =
      ((δ 1 0 : ℤ) : ℚ) * s + ((δ 1 1 : ℤ) : ℚ) * 1 at h11
  simp only [zero_mul, one_mul, zero_add, mul_one, mul_zero, add_zero] at h10 h00 h11
  exact ⟨by exact_mod_cast h10.symm, h00.symm, by simpa [add_comm] using h11.symm⟩

private theorem theta_conjugate_pos {m : ℕ} [NeZero m] (u v : ZMod m) (γ δ : SL(2, ℤ))
    (hc : (4 * (m : ℤ) ^ 2 : ℤ) ∣ γ 1 0) (hcpos : 0 < γ 1 0)
    (he : translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v)) (z : ℍ) :
    J δ (residueShift v +ᵥ z) = J γ z := by
  obtain ⟨hδc, ha, hd⟩ := conjugate_entries _ _ _ _ he
  obtain ⟨q, hq⟩ := hc
  have hqpos : 0 < q := pos_of_mul_pos_right (hq ▸ hcpos) (by positivity)
  lift q to ℕ using hqpos.le
  let C := 4 * (m ^ 2 * q)
  have hcγ : γ 1 0 = (C : ℤ) := by
    rw [hq]
    push_cast [C]
    ring
  let _ : NeZero C := ⟨fun h ↦ hcpos.ne' (by simp [hcγ, h])⟩
  have hcδ : δ 1 0 = (C : ℤ) := hδc.trans hcγ
  rw [J_at_cusp δ hcδ, J_at_cusp γ hcγ]
  have hQ (x : ZMod m) : ((ratShift x : ℚ) : ℂ) = (residueShift x : ℝ) := by
    rw [← ratShift_cast]
    norm_cast
  have hC : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
  have hm : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have htz : ((↑(residueShift v +ᵥ z) : ℂ) / 2 + ((δ 1 1 : ℤ) : ℂ) / (2 * (C : ℂ))) =
      (z : ℂ) / 2 + ((γ 1 1 : ℤ) : ℂ) / (2 * (C : ℂ)) := by
    rw [coe_vadd, ← hQ]
    rw [hcδ] at hd
    have hd' := congrArg (Rat.cast : ℚ → ℂ) hd
    push_cast at hd'
    field_simp
    linear_combination hd'
  change (1 / (-Complex.I * (-1 / (_ + _))) ^ (1 / 2 : ℂ)) * _ = _
  rw [htz]
  congr 1
  let a : ZMod C := (γ 0 0 : ℤ)
  let d : ZMod C := (γ 1 1 : ℤ)
  have had : a * d = 1 := by
    have hb := γ.det_coe
    rw [Matrix.det_fin_two, hcγ] at hb
    simpa [a, d, Int.cast_mul, Int.cast_sub] using congrArg (Int.cast : ℤ → ZMod C) hb
  let A : (ZMod C)ˣ := Units.mkOfMulEqOne a d had
  have ha' : δ 0 0 = γ 0 0 + 4 * (m : ℤ) * (q : ℤ) * (u.val : ℤ) := by
    rw [hcγ] at ha
    unfold ratShift at ha
    push_cast [C] at ha
    exact_mod_cast (show ((δ 0 0 : ℤ) : ℚ) = (γ 0 0 : ℤ) + 4 * (m : ℚ) * q * u.val by
      rw [ha]
      field_simp)
  rw [ha']
  push_cast
  exact quadraticFourier_translate m q A (u.val : ZMod C)

/-- The theta ratios of the two translation conjugates agree at every point
when the original bottom-left entry is divisible by `4m²`. -/
theorem theta_ratio_translate {m : ℕ} [NeZero m] (u v : ZMod m) (γ δ : SL(2, ℤ))
    (hc : (4 * (m : ℤ) ^ 2 : ℤ) ∣ γ 1 0)
    (he : translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v)) (z : ℍ) :
    jacobiTheta (2 * ((δ • (residueShift v +ᵥ z) : ℍ) : ℂ)) /
        jacobiTheta (2 * (↑(residueShift v +ᵥ z) : ℂ)) =
      jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ)) := by
  change J δ (residueShift v +ᵥ z) = J γ z
  rcases lt_trichotomy (γ 1 0) 0 with hn | hz | hp
  · have hc' : (4 * (m : ℤ) ^ 2 : ℤ) ∣ (-γ) 1 0 := by
      change _ ∣ -(γ 1 0)
      simpa using hc
    have hp' : 0 < (-γ) 1 0 := neg_pos.mpr hn
    have he' : translateMatrix (ratShift u) * (-γ).map (Int.castRingHom ℚ) =
        (-δ).map (Int.castRingHom ℚ) * translateMatrix (ratShift v) := by
      rw [coe_int_neg, coe_int_neg, mul_neg, neg_mul, neg_inj]
      exact he
    simpa only [J, ModularGroup.SL_neg_smul] using theta_conjugate_pos u v (-γ) (-δ) hc' hp' he' z
  · have hδ := (conjugate_entries _ _ _ _ he).1
    rw [J_of_c_zero hz, J_of_c_zero (hδ.trans hz)]
  · exact theta_conjugate_pos u v γ δ hc hp he z

#print axioms theta_pos_im
#print axioms coe_sl_smul
#print axioms J_of_c_zero
#print axioms J_at_cusp
#print axioms conjugate_entries
#print axioms theta_conjugate_pos
#print axioms theta_ratio_translate

end ZInQ.Manuscript.RC.HalfIntegral
