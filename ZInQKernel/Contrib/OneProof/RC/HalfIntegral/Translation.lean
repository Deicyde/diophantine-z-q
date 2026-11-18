import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Fourier
import ZInQKernel.Contrib.OneProof.RC.HalfIntegral.Cusps

/-! Passage of rational translations through congruence matrices, and the
holomorphy and cusp limits used by the twist (provenance (c)). -/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open UpperHalfPlane Filter Function CongruenceSubgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups Topology

theorem coe_rat_map_smul (γ : SL(2, ℤ)) (z : ℍ) :
    γ.map (Int.castRingHom ℚ) • z = γ • z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply (γ.map (Int.castRingHom ℚ)) z, coe_specialLinearGroup_apply γ z]
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

/-- At level `N³`, left translation by `u/N` moves through `γ` at the cost of a
right translation indexed by `d²u`. The resulting integral matrix has level
`N` and the same lower-right entry modulo `N`. -/
theorem exists_translation_conjugate {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 (N ^ 3)) (u : ZMod N) :
    let v := ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧
      ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
        δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v) := by
  dsimp only
  let a : ℤ := γ 0 0
  let b : ℤ := γ 0 1
  let c : ℤ := γ 1 0
  let d : ℤ := γ 1 1
  let v : ZMod N := (d : ZMod N) ^ 2 * u
  change ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ((δ 1 1 : ℤ) : ZMod N) = (d : ZMod N) ∧
    translateMatrix (ratShift u) * γ.map (Int.castRingHom ℚ) =
      δ.map (Int.castRingHom ℚ) * translateMatrix (ratShift v)
  have hd : a * d - b * c = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact h
  have hNN : N ∣ N ^ 3 := dvd_pow_self N (by decide)
  have hNc3 : (↑(N ^ 3) : ℤ) ∣ c :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  have hNc : (N : ℤ) ∣ c := dvd_trans (Int.natCast_dvd_natCast.mpr hNN) hNc3
  have hN2 : N ^ 2 ∣ N ^ 3 := ⟨N, by ring⟩
  have hNc2 : (↑(N ^ 2) : ℤ) ∣ c := dvd_trans (Int.natCast_dvd_natCast.mpr hN2) hNc3
  obtain ⟨q, hq⟩ := hNc2
  push_cast at hq
  have hc0 : (c : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc
  have had : (a : ZMod N) * d = 1 := by
    simpa [hc0] using congrArg (Int.cast : ℤ → ZMod N) hd
  obtain ⟨w, hw⟩ : (N : ℤ) ∣ a * (v.val : ℤ) - (u.val : ℤ) * d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [ZMod.natCast_zmod_val, v, pow_two, sub_eq_zero]
    linear_combination (d : ZMod N) * u * had
  let x : ℤ := u.val
  let y : ℤ := v.val
  change a * y - x * d = (N : ℤ) * w at hw
  let δ : SL(2, ℤ) := ⟨!![a + x * N * q, b - w - x * q * y; c, d - N * q * y], by
    rw [Matrix.det_fin_two]
    change (a + x * N * q) * (d - N * q * y) - (b - w - x * q * y) * c = 1
    linear_combination hd - (N : ℤ) * q * hw + (w + x * q * y) * hq⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · exact Gamma0_mem.mpr hc0
  · change ((d - (N : ℤ) * q * y : ℤ) : ZMod N) = (d : ZMod N)
    push_cast
    simp
  · have hn : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    have hq' := congrArg (Int.cast : ℤ → ℚ) hq
    have hw' := congrArg (Int.cast : ℤ → ℚ) hw
    push_cast at hq' hw'
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j
    · change 1 * (a : ℚ) + (x : ℚ) / N * (c : ℚ) =
        ((a + x * ↑N * q : ℤ) : ℚ) * 1 + ((b - w - x*q*y : ℤ) : ℚ) * 0
      push_cast
      rw [hq']
      field_simp
      ring
    · change 1 * (b : ℚ) + (x : ℚ) / N * (d : ℚ) =
        ((a + x * ↑N * q : ℤ) : ℚ) * ((y : ℚ) / N) + ((b - w - x*q*y : ℤ) : ℚ) * 1
      push_cast
      field_simp
      linear_combination -hw'
    · change 0 * (a : ℚ) + 1 * (c : ℚ) =
        (c : ℚ) * 1 + ((d - ↑N*q*y : ℤ) : ℚ) * 0
      ring
    · change 0 * (b : ℚ) + 1 * (d : ℚ) =
        (c : ℚ) * ((y : ℚ) / N) + ((d - ↑N*q*y : ℤ) : ℚ) * 1
      push_cast
      rw [hq']
      field_simp
      ring

theorem translate_differentiableOn {f : ℍ → ℂ}
    (hf : DifferentiableOn ℂ (f ∘ ofComplex) {z : ℂ | 0 < z.im}) (t : ℝ) :
    DifferentiableOn ℂ ((fun z : ℍ ↦ f (t +ᵥ z)) ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  have ht : Set.MapsTo (fun z : ℂ ↦ (t : ℂ) + z) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} :=
    fun z hz ↦ by simpa [Set.mem_ofPred_eq, Complex.add_im] using hz
  refine (hf.comp ((differentiableOn_const (t : ℂ)).add differentiableOn_id) ht).congr fun z hz ↦ ?_
  have hz' : 0 < ((t : ℂ) + z).im := ht hz
  simp [Function.comp_def, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
  rfl

theorem translationSum_cuspidal {N k : ℕ} [NeZero N] (v : ZMod N → ℂ) {f : ℍ → ℂ}
    (hf : ∀ α : SL(2, ℤ), Tendsto
      (fun z : ℍ ↦ ‖f (α • z)‖ * ‖denom (mapGL ℝ α) z‖ ^ (-(k : ℝ) / 2))
      atImInfty (𝓝 0)) (α : SL(2, ℤ)) :
    Tendsto (fun z : ℍ ↦ ‖translationSum v f (α • z)‖ *
      ‖denom (mapGL ℝ α) z‖ ^ (-(k : ℝ) / 2)) atImInfty (𝓝 0) := by
  let D (z : ℍ) := ‖denom (mapGL ℝ α) z‖ ^ (-(k : ℝ) / 2)
  have ht (u : ZMod N) :
      Tendsto (fun z : ℍ ↦ ‖translationWeights v u * f (residueShift u +ᵥ (α • z))‖ * D z)
        atImInfty (𝓝 0) := by
    have h := (ratTranslate_cuspidal hf (ratShift u) α).const_mul ‖translationWeights v u‖
    simpa [D, ratShift_cast, norm_mul, mul_assoc] using h
  have ht' := tendsto_finsetSum (s := (Finset.univ : Finset (ZMod N))) (fun u _ ↦ ht u)
  simp only [Finset.sum_const_zero] at ht'
  refine squeeze_zero (fun z ↦ by positivity) (fun z ↦ ?_) ht'
  rw [translationSum, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)

#print axioms coe_rat_map_smul
#print axioms exists_translation_conjugate
#print axioms translate_differentiableOn
#print axioms translationSum_cuspidal

end ZInQ.Manuscript.RC.HalfIntegral
