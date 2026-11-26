import ZInQKernel.Contrib.OneProof.WeberField

/-! # The period-pair Weierstrass data vary continuously with the parameter

For the lattice `ℤτ + ℤ`, the invariants `g₂, g₃` and the values `℘(1/N)`, `℘'(1/N)` are
holomorphic functions of τ on the upper half-plane. The first three are in the tree (Eisenstein
series and the locally uniform majorant of the ℘-series); the derivative uses the same majorant
for the absolutely convergent series `-2 ∑ (c - ω)⁻³`. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open UpperHalfPlane T5Glue X1Igusa.Weber

set_option maxHeartbeats 1000000

/-- The lattices of the two period pairs `(τ, 1)` and `(1, τ)` agree. -/
theorem ofTau_lattice_eq_ppD (τ : ℍ) : (PeriodPair.ofTau τ).lattice = (ppD τ).lattice := by
  change Submodule.span ℤ {(τ : ℂ), 1} = Submodule.span ℤ {1, (τ : ℂ)}
  rw [Set.pair_comm]

theorem g₂_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₂ = L₂.g₂ := by
  unfold PeriodPair.g₂ PeriodPair.G
  rw [h]

theorem g₃_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.g₃ = L₂.g₃ := by
  unfold PeriodPair.g₃ PeriodPair.G
  rw [h]

theorem weierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) (z : ℂ) :
    L₁.weierstrassP z = L₂.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  rw [h]

theorem derivWeierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) (z : ℂ) :
    L₁.derivWeierstrassP z = L₂.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  rw [h]

theorem continuous_g₂ : Continuous fun τ : ℍ => (PeriodPair.ofTau τ).g₂ := by
  have h := (diffOn_G2f.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    fun τ => τ.im_pos)
  refine h.congr fun τ => ?_
  simp only [Function.comp, G2f, ofComplex_apply]
  exact (g₂_congr (ofTau_lattice_eq_ppD τ)).symm

theorem continuous_g₃ : Continuous fun τ : ℍ => (PeriodPair.ofTau τ).g₃ := by
  have h := (diffOn_G3f.continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    fun τ => τ.im_pos)
  refine h.congr fun τ => ?_
  simp only [Function.comp, G3f, ofComplex_apply]
  exact (g₃_congr (ofTau_lattice_eq_ppD τ)).symm

theorem continuous_weierstrassP {N : ℕ} (hN : 2 ≤ N) :
    Continuous fun τ : ℍ => (PeriodPair.ofTau τ).weierstrassP (1 / N) := by
  have h := ((diffOn_Pf hN).continuousOn.comp_continuous UpperHalfPlane.continuous_coe
    fun τ => τ.im_pos)
  refine h.congr fun τ => ?_
  simp only [Function.comp, Pf, ofComplex_apply]
  exact (weierstrassP_congr (ofTau_lattice_eq_ppD τ) _).symm

/-- The terms of the series for `-℘'`. -/
noncomputable def dTerm (c : ℂ) (v : Fin 2 → ℤ) (w : ℂ) : ℂ :=
  2 / (c - ((v 0 : ℂ) * w + v 1)) ^ 3

theorem derivWeierstrassP_ppD_eq (τ : ℍ) (c : ℂ) :
    (ppD τ).derivWeierstrassP c = -∑' v : Fin 2 → ℤ, dTerm c v τ := by
  rw [PeriodPair.derivWeierstrassP, ← (latEquiv τ).tsum_eq]
  congr 2; funext v; rw [latEquiv_apply]; rfl

theorem diffOn_dTerm {c : ℝ} (hcZ : ∀ m : ℤ, c ≠ m) (v : Fin 2 → ℤ) :
    DifferentiableOn ℂ (dTerm c v) Hs := by
  unfold dTerm
  refine (differentiableOn_const _).div ?_ fun w hw => pow_ne_zero 3 (shift_ne_zero hcZ v hw)
  exact ((differentiableOn_const _).sub
    (((differentiableOn_const _).mul differentiableOn_id).add (differentiableOn_const _))).pow 3

theorem dTerm_bound {c : ℝ} (hc : |c| ≤ 1 / 2) {A B : ℝ} (hB : 0 < B) {v : Fin 2 → ℤ} (hv : v ≠ 0)
    {w : ℂ} (hw : |w.re| < A ∧ B < w.im) :
    ‖dTerm c v w‖ ≤ 16 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 3 * ‖v‖ ^ (-3 : ℝ) := by
  set r₀ := EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ with hr₀
  have hr₀p : 0 < r₀ := EisensteinSeries.r_pos _
  have hwH : 0 < w.im := lt_trans hB hw.2
  set τ : UpperHalfPlane := ⟨w, hwH⟩ with hτ
  have hstrip : τ ∈ verticalStrip A B := ⟨hw.1.le, hw.2.le⟩
  have hrr : r₀ ≤ EisensteinSeries.r τ := EisensteinSeries.r_lower_bound_on_verticalStrip τ hB hstrip
  have hm := one_le_norm_vec hv
  set m := ‖v‖ with hmdef
  have hm0 : 0 < m := by linarith
  have hδb : r₀ * m ≤ 2 * ‖(c : ℂ) - ((v 0 : ℂ) * w + v 1)‖ := by
    have := shift_bound τ hv hc
    calc r₀ * m ≤ EisensteinSeries.r τ * m := by gcongr
      _ ≤ _ := this
  set δ := (c : ℂ) - ((v 0 : ℂ) * w + v 1)
  have hδp : 0 < ‖δ‖ := by nlinarith
  unfold dTerm
  rw [norm_div, norm_pow, RCLike.norm_ofNat]
  have h3 : m ^ (-3 : ℝ) = (m ^ 3)⁻¹ := by
    rw [Real.rpow_neg hm0.le, ← Real.rpow_natCast]; norm_num
  rw [h3]
  have hpos : 0 < r₀ * m / 2 := by positivity
  have hle : r₀ * m / 2 ≤ ‖δ‖ := by linarith
  have hlow : (r₀ * m / 2) ^ 3 ≤ ‖δ‖ ^ 3 := pow_le_pow_left₀ hpos.le hle 3
  calc 2 / ‖δ‖ ^ 3 ≤ 2 / (r₀ * m / 2) ^ 3 :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos hpos 3) hlow
    _ = 16 / r₀ ^ 3 * (m ^ 3)⁻¹ := by field_simp; ring

theorem diffOn_tsum_dTerm {c : ℝ} (hc : |c| ≤ 1 / 2) (hcZ : ∀ m : ℤ, c ≠ m) :
    DifferentiableOn ℂ (fun z => ∑' v : Fin 2 → ℤ, dTerm c v z) Hs := by
  intro z₀ hz₀
  have hz₀' : 0 < z₀.im := hz₀
  set A := |z₀.re| + 1
  set B := z₀.im / 2
  have hB : 0 < B := by positivity
  set U : Set ℂ := {w | |w.re| < A ∧ B < w.im} with hU
  have hUo : IsOpen U :=
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hz₀U : z₀ ∈ U := ⟨by simp [A], by simp only [B]; linarith⟩
  have hUH : U ⊆ Hs := fun w hw => lt_trans hB hw.2
  set K := 16 / EisensteinSeries.r ⟨⟨A, B⟩, hB⟩ ^ 3
  classical
  set u : (Fin 2 → ℤ) → ℝ := Function.update (fun v => K * ‖v‖ ^ (-3 : ℝ)) 0 ‖2 / (c : ℂ) ^ 3‖
  have hu : Summable u :=
    ((EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)).mul_left K).update _ _
  have hd : DifferentiableOn ℂ (fun z => ∑' v : Fin 2 → ℤ, dTerm c v z) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hu
      (fun v => (diffOn_dTerm hcZ v).mono hUH) hUo ?_
    intro v w hw
    by_cases hv : v = 0
    · subst hv
      simp [u, dTerm]
    · simp only [u, Function.update_of_ne hv]
      exact dTerm_bound hc hB hv hw
  exact (hd.differentiableAt (hUo.mem_nhds hz₀U)).differentiableWithinAt

theorem continuous_derivWeierstrassP {N : ℕ} (hN : 2 ≤ N) :
    Continuous fun τ : ℍ => (PeriodPair.ofTau τ).derivWeierstrassP (1 / N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : |(1 / N : ℝ)| ≤ 1 / 2 := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by norm_num) hN'
  have hcZ : ∀ m : ℤ, (1 / N : ℝ) ≠ m := by
    intro m hm
    have h0 : (0 : ℝ) < 1 / N := by positivity
    have h1 : (1 / N : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    rw [hm] at h0 h1
    have : (0 : ℤ) < m := by exact_mod_cast h0
    have : m < (1 : ℤ) := by exact_mod_cast h1
    omega
  have h := ((diffOn_tsum_dTerm hc hcZ).continuousOn.comp_continuous
    UpperHalfPlane.continuous_coe fun τ => τ.im_pos).neg
  refine h.congr fun τ => ?_
  simp only [Function.comp, Pi.neg_apply]
  rw [derivWeierstrassP_congr (ofTau_lattice_eq_ppD τ), derivWeierstrassP_ppD_eq]
  push_cast
  rfl

#print axioms continuous_g₂
#print axioms continuous_g₃
#print axioms continuous_weierstrassP
#print axioms continuous_derivWeierstrassP

end WeierstrassCurve.ModelLevels.ModelGeneric4
