import ZInQKernel.HDecomp.Analytic.Torus

/-!
# Normal convergence of the Riemann theta series

The positive definite imaginary part of the period matrix bounds the
quadratic term below. This gives a product of Mathlib's one-variable
Jacobi theta bounds on any strip with bounded imaginary coordinates.
The same estimate, with a larger strip bound, controls the norms of the
Taylor coefficients before summing over the lattice.

The series and its convention are those of DLMF §21.2, Eq. (21.2.1).
-/

open scoped Topology NNReal ENNReal ContDiff
open Set Filter Matrix Complex

noncomputable section

namespace BPAnalytic

variable {g : ℕ}

/-- A term of the defining series of the Riemann theta function. -/
def riemannThetaSummand (Ω : Matrix (Fin g) (Fin g) ℂ) (n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  exp (Real.pi * I * (intVec n ⬝ᵥ (Ω *ᵥ intVec n)) + 2 * Real.pi * I * (intVec n ⬝ᵥ z))

private theorem quadratic_lower_bound {Y : Matrix (Fin g) (Fin g) ℝ} (hY : Y.PosDef) :
    ∃ a > 0, ∀ x : Fin g → ℝ, a * (∑ j, (x j) ^ 2) ≤ x ⬝ᵥ (Y *ᵥ x) := by
  let q : (Fin g → ℝ) → ℝ := fun x => x ⬝ᵥ (Y *ᵥ x)
  have hq : Continuous q := by
    dsimp only [q]
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hpos : ∀ x ∈ Metric.sphere (0 : Fin g → ℝ) 1, 0 < q x := by
    intro x hx
    have hnorm : ‖x‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hx
    have hne : x ≠ 0 := by
      intro hz
      simp [hz] at hnorm
    simpa [q] using hY.dotProduct_mulVec_pos hne
  obtain ⟨c, hc, hmin⟩ :=
    (isCompact_sphere (0 : Fin g → ℝ) 1).exists_forall_le' hq.continuousOn hpos
  let a : ℝ := c / ((g : ℝ) + 1)
  have ha : 0 < a := div_pos hc (by positivity)
  refine ⟨a, ha, ?_⟩
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y := ‖x‖⁻¹ • x
  have hy : y ∈ Metric.sphere (0 : Fin g → ℝ) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    change ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
  have hxy : x = ‖x‖ • y := by
    dsimp only [y]
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hscale : q (‖x‖ • y) = ‖x‖ ^ 2 * q y := by
    simp only [q, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hs : (∑ j, (x j) ^ 2) ≤ ((g : ℝ) + 1) * ‖x‖ ^ 2 := calc
    _ ≤ ∑ _ : Fin g, ‖x‖ ^ 2 := Finset.sum_le_sum fun j _ => by
      apply sq_le_sq.mpr
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] using norm_le_pi_norm x j
    _ = (g : ℝ) * ‖x‖ ^ 2 := by simp [nsmul_eq_mul]
    _ ≤ ((g : ℝ) + 1) * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)
  calc
    a * (∑ j, (x j) ^ 2) ≤ a * (((g : ℝ) + 1) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hs ha.le
    _ = c * ‖x‖ ^ 2 := by
      dsimp only [a]
      rw [← mul_assoc, div_mul_cancel₀ _ (by positivity)]
    _ ≤ q (‖x‖ • y) := by
      rw [hscale, mul_comm c]
      exact mul_le_mul_of_nonneg_left (hmin y hy) (sq_nonneg _)
    _ = q x := congrArg q hxy.symm

private theorem summable_fin_product {u : ℤ → ℝ} (hu : Summable u) (hu₀ : 0 ≤ u) (d : ℕ) :
    Summable (fun n : Fin d → ℤ => ∏ j, u (n j)) := by
  induction d with
  | zero =>
    let _ : Subsingleton (Fin 0 → ℤ) := ⟨fun _ _ => funext (fun j => Fin.elim0 j)⟩
    let _ : Fintype (Fin 0 → ℤ) := Fintype.ofSubsingleton 0
    exact (hasSum_fintype _).summable
  | succ d ih =>
    have hp : Summable (fun p : (Fin d → ℤ) × ℤ => (∏ j, u (p.1 j)) * u p.2) :=
      ih.mul_of_nonneg hu (fun n => Finset.prod_nonneg fun j _ => hu₀ (n j)) hu₀
    have h := (Fin.succFunEquiv ℤ d).summable_iff.mpr hp
    change Summable (fun n : Fin (d + 1) → ℤ =>
      (∏ j : Fin d, u (n j.castSucc)) * u (n (Fin.last d))) at h
    have hprod (n : Fin (d + 1) → ℤ) :
        (∏ j, u (n j)) = (∏ j : Fin d, u (n j.castSucc)) * u (n (Fin.last d)) :=
      Fin.prod_univ_castSucc (fun j => u (n j))
    simpa only [hprod] using h

private theorem im_intVec_dotProduct (n : Fin g → ℤ) (z : Fin g → ℂ) :
    (intVec n ⬝ᵥ z).im = ∑ j, (n j : ℝ) * (z j).im := by
  simp [intVec, dotProduct, Complex.im_sum, Complex.mul_im]

private theorem im_mulVec_intVec (Ω : Matrix (Fin g) (Fin g) ℂ) (n : Fin g → ℤ) (j : Fin g) :
    ((Ω *ᵥ intVec n) j).im = ((Ω.map Complex.im) *ᵥ (fun i => (n i : ℝ))) j := by
  simp [intVec, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

private theorem norm_riemannThetaSummand (Ω : Matrix (Fin g) (Fin g) ℂ)
    (n : Fin g → ℤ) (z : Fin g → ℂ) :
    ‖riemannThetaSummand Ω n z‖ =
      Real.exp (-Real.pi * ((fun j => (n j : ℝ)) ⬝ᵥ ((Ω.map Complex.im) *ᵥ (fun j => (n j : ℝ))) +
        2 * (∑ j, (n j : ℝ) * (z j).im))) := by
  let a := intVec n ⬝ᵥ (Ω *ᵥ intVec n)
  let b := intVec n ⬝ᵥ z
  have ha : a.im = (fun j => (n j : ℝ)) ⬝ᵥ ((Ω.map Complex.im) *ᵥ (fun j => (n j : ℝ))) := by
    change (intVec n ⬝ᵥ (Ω *ᵥ intVec n)).im = _
    rw [im_intVec_dotProduct]
    simp only [im_mulVec_intVec, dotProduct]
  have hb : b.im = ∑ j, (n j : ℝ) * (z j).im := im_intVec_dotProduct n z
  change ‖exp ((Real.pi : ℂ) * I * a + 2 * Real.pi * I * b)‖ = _
  rw [Complex.norm_exp]
  apply congrArg Real.exp
  rw [show (Real.pi : ℂ) * I * a + 2 * Real.pi * I * b =
    (Real.pi : ℂ) * a * I + ((2 * Real.pi : ℝ) : ℂ) * b * I by push_cast; ring]
  rw [add_re, mul_I_re, im_ofReal_mul, mul_I_re, im_ofReal_mul, ha, hb]
  ring

private theorem exists_summable_weighted_bound (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (R r : ℝ) :
    ∃ u : (Fin g → ℤ) → ℝ, Summable u ∧
      ∀ n z, (∀ j, |(z j).im| ≤ R) →
        ‖riemannThetaSummand Ω n z‖ * Real.exp (2 * Real.pi * r * (∑ j, |(n j : ℝ)|)) ≤ u n := by
  obtain ⟨a, ha, hquad⟩ := quadratic_lower_bound hΩ.2
  let u : ℤ → ℝ := fun k => Real.exp (-Real.pi * (a * (k : ℝ) ^ 2 - 2 * (R + r) * |(k : ℝ)|))
  have hu : Summable u := by
    simpa only [u, pow_zero, one_mul, Int.cast_abs] using
      summable_pow_mul_jacobiTheta₂_term_bound (R + r) ha 0
  refine ⟨fun n => ∏ j, u (n j), summable_fin_product hu (fun _ => (Real.exp_pos _).le) g, ?_⟩
  intro n z hz
  have hlin : -(R * ∑ j, |(n j : ℝ)|) ≤ ∑ j, (n j : ℝ) * (z j).im := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    calc
      -(R * |(n j : ℝ)|) ≤ -(|(n j : ℝ)| * |(z j).im|) := by
        rw [neg_le_neg_iff, mul_comm R]
        exact mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
      _ ≤ (n j : ℝ) * (z j).im := by rw [← abs_mul]; exact neg_abs_le _
  let x : Fin g → ℝ := fun j => n j
  let Q := x ⬝ᵥ ((Ω.map Complex.im) *ᵥ x)
  let d := ∑ j, (n j : ℝ) * (z j).im
  let A := ∑ j, |(n j : ℝ)|
  have hb : a * (∑ j, (x j) ^ 2) - 2 * (R + r) * A ≤ Q + 2 * d - 2 * r * A := by
    dsimp only [Q, d, A]
    linarith only [hquad x, hlin]
  simp only [u, norm_riemannThetaSummand, ← Real.exp_add, ← Real.exp_sum, Real.exp_le_exp]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change -Real.pi * (Q + 2 * d) + 2 * Real.pi * r * A ≤
    -Real.pi * (a * (∑ j, (x j) ^ 2) - 2 * (R + r) * A)
  calc
    _ = -Real.pi * (Q + 2 * d - 2 * r * A) := by ring
    _ ≤ _ := mul_le_mul_of_nonpos_left hb (neg_nonpos.mpr Real.pi_pos.le)

/-- A single summable bound works for all arguments with imaginary coordinates bounded by `R`. -/
theorem exists_summable_riemannThetaSummand_bound (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (R : ℝ) :
    ∃ u : (Fin g → ℤ) → ℝ, Summable u ∧
      ∀ n z, (∀ j, |(z j).im| ≤ R) → ‖riemannThetaSummand Ω n z‖ ≤ u n := by
  obtain ⟨u, hu, hbound⟩ := exists_summable_weighted_bound Ω hΩ R 0
  exact ⟨u, hu, by simpa using hbound⟩

theorem summable_norm_riemannThetaSummand (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ω ∈ SiegelSpace g)
    (z : Fin g → ℂ) : Summable (fun n => ‖riemannThetaSummand Ω n z‖) := by
  obtain ⟨u, hu, hbound⟩ := exists_summable_riemannThetaSummand_bound Ω hΩ ‖z‖
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => hbound n z fun j => (Complex.abs_im_le_norm (z j)).trans (norm_le_pi_norm z j)) hu

/-- The series converges uniformly on strips, hence locally uniformly on the covering space. -/
theorem tendstoUniformlyOn_riemannTheta (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ω ∈ SiegelSpace g)
    (R : ℝ) :
    TendstoUniformlyOn (fun s : Finset (Fin g → ℤ) => fun z => ∑ n ∈ s, riemannThetaSummand Ω n z)
      (riemannTheta Ω) atTop {z | ∀ j, |(z j).im| ≤ R} := by
  obtain ⟨u, hu, hbound⟩ := exists_summable_riemannThetaSummand_bound Ω hΩ R
  exact tendstoUniformlyOn_tsum hu hbound

private def thetaLinearForm (n : Fin g → ℤ) : (Fin g → ℂ) →L[ℂ] ℂ :=
  (2 * (Real.pi : ℂ) * I) • ∑ j, intVec n j • ContinuousLinearMap.proj j

private theorem thetaLinearForm_apply (n : Fin g → ℤ) (y : Fin g → ℂ) :
    thetaLinearForm n y = 2 * Real.pi * I * (intVec n ⬝ᵥ y) := by
  simp [thetaLinearForm, dotProduct, _root_.sum_apply, smul_eq_mul]

private theorem norm_thetaLinearForm_le (n : Fin g → ℤ) :
    ‖thetaLinearForm n‖ ≤ 2 * Real.pi * (∑ j, |(n j : ℝ)|) := by
  rw [thetaLinearForm, norm_smul]
  simp only [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le, norm_I, mul_one]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  let p : (Fin g → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj j
  have hp : ‖p‖ ≤ 1 :=
    p.opNorm_le_bound zero_le_one (fun y => by simpa [p] using norm_le_pi_norm y j)
  change ‖intVec n j • p‖ ≤ _
  rw [norm_smul]
  simp only [intVec, Complex.norm_intCast]
  exact mul_le_of_le_one_right (abs_nonneg _) hp

private def thetaTaylorCoefficient (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ)
    (n : Fin g → ℤ) (k : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin k => Fin g → ℂ) ℂ :=
  riemannThetaSummand Ω n z • (NormedSpace.expSeries ℂ ℂ k).compContinuousLinearMap
    (fun _ => thetaLinearForm n)

private theorem norm_thetaTaylorCoefficient_le (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ)
    (n : Fin g → ℤ) (k : ℕ) :
    ‖thetaTaylorCoefficient Ω z n k‖ ≤
      ‖riemannThetaSummand Ω n z‖ * (‖thetaLinearForm n‖ ^ k / (k.factorial : ℝ)) := by
  rw [thetaTaylorCoefficient, norm_smul]
  refine mul_le_mul_of_nonneg_left
    ((ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq ?_) (norm_nonneg _)
  rw [NormedSpace.expSeries, norm_smul, ContinuousMultilinearMap.norm_mkPiAlgebraFin, mul_one,
    norm_inv, Complex.norm_natCast]
  simp [div_eq_mul_inv, mul_comm]

private theorem summable_thetaTaylorCoefficient_norm (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : Ω ∈ SiegelSpace g) (z : Fin g → ℂ) :
    Summable (fun p : ℕ × (Fin g → ℤ) => ‖thetaTaylorCoefficient Ω z p.2 p.1‖) := by
  let B : (Fin g → ℤ) × ℕ → ℝ := fun p =>
    ‖riemannThetaSummand Ω p.1 z‖ * (‖thetaLinearForm p.1‖ ^ p.2 / (p.2.factorial : ℝ))
  have hB₀ (p : (Fin g → ℤ) × ℕ) : 0 ≤ B p := by
    dsimp only [B]
    positivity
  have hB (n : Fin g → ℤ) :
      HasSum (fun k => B (n, k)) (‖riemannThetaSummand Ω n z‖ * Real.exp ‖thetaLinearForm n‖) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ‖thetaLinearForm n‖).mul_left ‖riemannThetaSummand Ω n z‖
  obtain ⟨u, hu, hbound⟩ := exists_summable_weighted_bound Ω hΩ ‖z‖ 1
  have houter : Summable (fun n => ∑' k, B (n, k)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hu
    · rw [(hB n).tsum_eq]
      positivity
    · rw [(hB n).tsum_eq]
      refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (norm_thetaLinearForm_le n))
        (norm_nonneg _)).trans ?_
      simpa only [mul_one] using
        hbound n z (fun j => (Complex.abs_im_le_norm (z j)).trans (norm_le_pi_norm z j))
  have hsum : Summable B :=
    (summable_prod_of_nonneg hB₀).mpr ⟨fun n => (hB n).summable, houter⟩
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => norm_thetaTaylorCoefficient_le Ω z p.2 p.1)
    ((Equiv.prodComm ℕ (Fin g → ℤ)).summable_iff.mpr hsum)

private theorem tsum_thetaTaylorCoefficient (Ω : Matrix (Fin g) (Fin g) ℂ)
    (z y : Fin g → ℂ) (n : Fin g → ℤ) :
    (∑' k, thetaTaylorCoefficient Ω z n k (fun _ => y)) = riemannThetaSummand Ω n (z + y) := by
  calc
    _ = riemannThetaSummand Ω n z * Complex.exp (thetaLinearForm n y) := by
      rw [Complex.exp_eq_exp_ℂ, ← (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ)
        (thetaLinearForm n y)).tsum_eq, ← tsum_mul_left]
      rfl
    _ = _ := by
      simp only [riemannThetaSummand, thetaLinearForm_apply, ← Complex.exp_add, dotProduct_add]
      congr 1
      ring

set_option maxHeartbeats 1000000 in
/-- The Riemann theta function of a Siegel matrix is entire in its argument. -/
theorem analyticAt_riemannTheta (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ω ∈ SiegelSpace g)
    (z : Fin g → ℂ) : AnalyticAt ℂ (riemannTheta Ω) z := by
  let p : FormalMultilinearSeries ℂ (Fin g → ℂ) ℂ := fun k => ∑' n, thetaTaylorCoefficient Ω z n k
  have hc := summable_thetaTaylorCoefficient_norm Ω hΩ z
  have hp : Summable (fun k => ‖p k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => norm_tsum_le_tsum_norm (hc.prod_factor k)) hc.prod
  have hr : (1 : ℝ≥0∞) ≤ p.radius := by
    simpa using (p.le_radius_of_summable_norm (r := 1) (by simpa using hp))
  refine ⟨p, ⟨1, hr, zero_lt_one, ?_⟩⟩
  intro y hy
  have hy₁ : ‖y‖ ≤ 1 := by
    have hb : y ∈ Metric.eball (0 : Fin g → ℂ) (↑(1 : ℝ≥0) : ℝ≥0∞) := by simpa using hy
    exact le_of_lt (by simpa only [Metric.eball_coe, Metric.mem_ball, dist_zero_right, NNReal.coe_one]
      using hb)
  let f : ℕ → (Fin g → ℤ) → ℂ := fun k n => thetaTaylorCoefficient Ω z n k (fun _ => y)
  have hf : Summable (Function.uncurry f) := by
    refine (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hc).of_norm
    intro q
    change ‖thetaTaylorCoefficient Ω z q.2 q.1 (fun _ => y)‖ ≤ ‖thetaTaylorCoefficient Ω z q.2 q.1‖
    refine ((thetaTaylorCoefficient Ω z q.2 q.1).le_opNorm _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy₁)
  have heval (k : ℕ) : p k (fun _ => y) = ∑' n, f k n :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k => Fin g → ℂ) ℂ
      (fun _ => y)).map_tsum (hc.prod_factor k).of_norm
  have hsum : (∑' k, ∑' n, f k n) = riemannTheta Ω (z + y) := calc
    _ = ∑' n, ∑' k, f k n := hf.tsum_comm.symm
    _ = ∑' n, riemannThetaSummand Ω n (z + y) :=
      tsum_congr (tsum_thetaTaylorCoefficient Ω z y)
  simp_rw [heval]
  rw [← hsum]
  exact hf.prod.hasSum

theorem contDiff_riemannTheta (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ω ∈ SiegelSpace g) :
    ContDiff ℂ ω (riemannTheta Ω) :=
  contDiff_iff_contDiffAt.mpr fun z => (analyticAt_riemannTheta Ω hΩ z).contDiffAt

end BPAnalytic
