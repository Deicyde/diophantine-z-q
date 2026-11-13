
/-! ## period-map: `OmegaSiegel` proved (closed form of `Ω(τ)`)

`Ω(τ) = adj(F₀P⁻¹)E / det(F₀P⁻¹)` with `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2` and the adjugate product `Nf`
computed by `py/omega_lean.py` (entries reduced mod `√2² = 2`; the `linear_combination` coefficients
are the quotients printed there). With `τ = x + iy`, `Im Ω_ij = A_ij/|d|²` where
`A₀₀ = (y/2)((4−√2)(x²+y²) − 6√2x + 12 + 3√2)`, `A₁₁ = 2A₀₀`, and
`A₀₀A₁₁ − A₀₁² = 3y²|τ−3|²|τ+1|²`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Matrix

/-- `det(F₀(τ)P⁻¹)`. -/
def dF (τ : ℂ) : ℂ := -(√2 : ℂ) * (τ - 3) * (τ + 1) / 2

/-- `adj(F₀(τ)P⁻¹)·E(τ)`, entries reduced mod `√2² = 2`. -/
def Nf (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(√2 : ℂ) * (τ ^ 2 / 2 + τ - 3 / 2) - τ ^ 2 / 2 - 3 / 2,
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3;
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3,
     (√2 : ℂ) * (τ ^ 2 + 2 * τ - 3) - τ ^ 2 - 3]

theorem adjE_eq (τ : ℂ) : adjugate (PkgI1.F0mat τ * PkgI1.Pinv) * PkgI1.Emat τ = Nf τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, PkgI1.Pinv,
      PkgI1.Emat, latVec_apply, PkgI1.iota, PkgI1.Mi, PkgI1.Mj, PkgI1.oBasis, Nf]
  · ring
  · linear_combination (τ ^ 2 / 2 + 3 / 2) * sqrt2_sq
  · ring
  · linear_combination (-τ ^ 2 / 2 - 3 / 2) * sqrt2_sq

theorem omega_eq (τ : ℂ) (i j : Fin 2) : PkgI1.Omega τ i j = Nf τ i j / dF τ := by
  have h : PkgI1.Omega τ = (PkgI1.F0mat τ * PkgI1.Pinv)⁻¹ * PkgI1.Emat τ := rfl
  rw [h, Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    adjE_eq, det_F0P, dF]
  ring

/-- `A₀₀/(y/2)`. -/
def Qf (x y : ℝ) : ℝ := (4 - √2) * (x ^ 2 + y ^ 2) - 6 * √2 * x + 12 + 3 * √2

theorem Qf_pos (x y : ℝ) : 0 < Qf x y := by
  have hs := sqrt2_sq'
  have h4 : 0 < 4 - √2 := by
    have : √2 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hid : (4 - √2) * Qf x y = ((4 - √2) * x - 3 * √2) ^ 2 + ((4 - √2) * y) ^ 2 + 24 := by
    unfold Qf; linear_combination (-12 : ℝ) * hs
  have : 0 < (4 - √2) * Qf x y := by rw [hid]; positivity
  exact pos_of_mul_pos_right this h4.le

theorem A00_eq (τ : ℂ) :
    (Nf τ 0 0).im * (dF τ).re - (Nf τ 0 0).re * (dF τ).im = τ.im / 2 * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (τ.re ^ 2 * τ.im + τ.im ^ 3 + 3 * τ.im) * sqrt2_sq'

theorem A01_eq (τ : ℂ) : (Nf τ 0 1).im * (dF τ).re - (Nf τ 0 1).re * (dF τ).im =
    τ.im * (√2 * τ.re ^ 2 + 6 * √2 * τ.re + √2 * τ.im ^ 2 - 3 * √2 - 2 * τ.re ^ 2 -
      2 * τ.im ^ 2 - 6) := by
  simp [Nf, dF, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (-τ.re ^ 2 * τ.im - τ.im ^ 3 - 3 * τ.im) * sqrt2_sq'

theorem A11_eq (τ : ℂ) :
    (Nf τ 1 1).im * (dF τ).re - (Nf τ 1 1).re * (dF τ).im = τ.im * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (2 * τ.re ^ 2 * τ.im + 2 * τ.im ^ 3 + 6 * τ.im) * sqrt2_sq'

theorem det_A (x y : ℝ) :
    y / 2 * Qf x y * (y * Qf x y) - y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6) * (y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6)) =
      3 * y ^ 2 * ((x - 3) ^ 2 + y ^ 2) * ((x + 1) ^ 2 + y ^ 2) := by
  unfold Qf
  linear_combination (-x ^ 4 * y ^ 2 / 2 - 6 * x ^ 3 * y ^ 2 - x ^ 2 * y ^ 4 - 15 * x ^ 2 * y ^ 2 -
    6 * x * y ^ 4 + 18 * x * y ^ 2 - y ^ 6 / 2 + 3 * y ^ 4 - 9 * y ^ 2 / 2) * sqrt2_sq'

/-- A real symmetric `2 × 2` matrix with `M₀₀ > 0` and `det M > 0` is positive definite. -/
theorem posDef_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} (hs : M 1 0 = M 0 1) (h0 : 0 < M 0 0)
    (hd : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hs]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [hs] at hd ⊢
    by_cases h1 : v 1 = 0
    · have h0' : v 0 ≠ 0 := by
        intro h; apply hv; funext i; fin_cases i <;> simp [h, h1]
      rw [h1]
      have : 0 < v 0 * v 0 := mul_self_pos.mpr h0'
      nlinarith
    · have : 0 < v 1 * v 1 := mul_self_pos.mpr h1
      have key : M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) =
          (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 0 1) * (v 1 * v 1) := by ring
      have hpos : 0 < M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) +
          v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) := by
        rw [key]; positivity
      exact pos_of_mul_pos_right hpos h0.le

/-- **`OmegaSiegel` (proved).** -/
theorem omegaSiegel_proof : OmegaSiegel := by
  intro τ hτ
  have hne : dF τ ≠ 0 := by
    have := det_F0P_ne hτ.ne'
    rwa [det_F0P] at this
  have hn : 0 < Complex.normSq (dF τ) := Complex.normSq_pos.mpr hne
  have him : ∀ i j, (PkgI1.Omega τ i j).im =
      ((Nf τ i j).im * (dF τ).re - (Nf τ i j).re * (dF τ).im) / Complex.normSq (dF τ) := by
    intro i j
    rw [omega_eq, Complex.div_im]
    ring
  have hsym : PkgI1.Omega τ 1 0 = PkgI1.Omega τ 0 1 := by
    rw [omega_eq, omega_eq]; rfl
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hsym]
  · apply posDef_fin_two
    · simp only [Matrix.map_apply, hsym]
    · simp only [Matrix.map_apply]
      rw [him, A00_eq]
      exact div_pos (mul_pos (half_pos hτ) (Qf_pos _ _)) hn
    · simp only [Matrix.map_apply]
      rw [hsym, him 0 0, him 1 1, him 0 1, A00_eq, A11_eq, A01_eq]
      rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, det_A]
      apply div_pos _ (mul_pos hn hn)
      have h3 : 0 < (τ.re - 3) ^ 2 + τ.im ^ 2 := by positivity
      have h1 : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by positivity
      positivity

/-- **`ThetaOmegaAnalytic` (proved).** -/
theorem thetaOmegaAnalytic_proof : ThetaOmegaAnalytic := thetaOmegaAnalytic_of omegaSiegel_proof

/-- **`HauptmodulUnique` from `S8Nonzero` and `SphereFactorAffine` (proved).** -/
theorem hauptmodulUnique_of' (hS : S8Nonzero) (hSF : SphereFactorAffine) : HauptmodulUnique :=
  hauptmodulUnique_of thetaOmegaAnalytic_proof hS hSF

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8Weight8`, `S8OrderCM3` and `ValenceBoundGammaStar`
(proved).** -/
theorem qmDenZeroCM3_of' (hS : S8Nonzero) (hW : S8Weight8) (hO : S8OrderCM3)
    (hV : ValenceBoundGammaStar) : QMDenZeroCM3 :=
  qmDenZeroCM3_of thetaOmegaAnalytic_proof hS hW hO hV

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMap.thetaOmegaAnalytic_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMap.hauptmodulUnique_of'
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'
