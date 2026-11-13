
/-! ## period-map: `S8Weight8` and `S8OrderCM3` from the exact automorphy `S8WeightExact`

`S8WeightExact` (`G8(γτ)·det γ⁴ = (cτ + d)⁸ G8(τ)` on `Γ*`, trivial multiplier; VERIFIED
numerically, `py/multiplier.py`) implies the absolute-value form `S8Weight8` (`s8Weight8_of`) and,
at the elliptic element `γ₃ = ι((1+j)/2)` fixing `i√3` with `cτ₃ + d = w = e^{iπ/3}`, the vanishing
order `S8OrderCM3` (`s8OrderCM3_of`): `G8(τ₃) = w⁸G8(τ₃)` with `w⁸ ≠ 1` gives `G8(τ₃) = 0`;
differentiating `G8 ∘ γ₃ = (cτ + d)⁸ G8` at `τ₃` gives `G8'(τ₃)(1 − w¹⁰) = 0` with `w¹⁰ = −w ≠ 1`;
so `ord_{τ₃} G8 ≥ 2`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology
open UpperHalfPlane (num denom denom_ne_zero)

/-- **GLUE (exact automorphy of `G8 = Σθ⁸∘Ω/((τ−3)(τ+1))⁴` under `Γ*`, trivial multiplier).**
For `γ ∈ Γ*` and `τ ∈ ℍ`, `G8(γτ)·det(γ)⁴ = (cτ + d)⁸ G8(τ)`.

VERIFIED numerically (`py/multiplier.py`, `multiplier_out.txt`, mpmath 40 digits): the ratio
`G8(γτ) det γ⁴/((cτ+d)⁸ G8(τ))` is `1` (to 9-40 digits) for `γ = ι(x)`, `x = (1+j)/2, j, i+j, 3+2i,
2j+ij, 1+i+j, 2+i`, at two points each; these include the elliptic generators of orders 2, 4, 6
(`py/gen_check.py`) and the Atkin–Lehner elements of norms 2, 3, 6. Why true: for `γ ∈ Γ*` the
principally polarized QM surfaces at `τ` and `γτ` are isomorphic, so `Ω(γτ) = M_γ·Ω(τ)` with
`M_γ ∈ Sp₄(ℤ)`; Igusa's `ThetaModularity` (pkg-I1 leaf) gives
`Σθ⁸(Ω(γτ)) = det(CΩ + D)⁴ Σθ⁸(Ω(τ))`, and `det(CΩ(τ) + D) = ±(cτ + d)² dF(γτ)/(det γ · dF(τ))`
from the explicit `Ω` (finite computation per generator of `Γ*`; that the tested elements generate
`Γ*` is the presentation of the `(2,4,6)` triangle group, not checked here). Size: medium. -/
def S8WeightExact : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
    G8 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ z ^ 8 * G8 (z : ℂ)

/-- **`S8Weight8` from `S8WeightExact` (proved).** -/
theorem s8Weight8_of (h : S8WeightExact) : S8Weight8 := by
  intro γ hγ z
  have ⟨_, _, _, hdet⟩ := hγ
  have e := congrArg norm (h γ hγ z)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
  exact e

theorem G8_analytic (hT : ThetaOmegaAnalytic) : AnalyticOnNhd ℂ G8 U := by
  intro z hz
  have hz' : (0 : ℝ) < z.im := hz
  have hdF : ((z - 3) * (z + 1)) ^ 4 ≠ 0 := by
    apply pow_ne_zero
    apply mul_ne_zero <;> intro h0 <;> have := congrArg Complex.im h0 <;> simp at this <;>
      exact hz'.ne' this
  exact (hT.1 z hz).div ((((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.add analyticAt_const))).pow 4) hdF

/-- `𝒪` is closed under multiplication (pkg-I1's membership; the coordinates of a product are
LeafQM's `mulCoord`). -/
theorem inO_mul {a b : PkgI1.B} (ha : PkgI1.InO a) (hb : PkgI1.InO b) : PkgI1.InO (a * b) := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  refine ⟨![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0], ?_⟩
  ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- `(1 − j)/2 = x₃⁻¹`. -/
def x3inv : PkgI1.B := ⟨1/2, 0, -1/2, 0⟩

theorem inO_x3inv : PkgI1.InO x3inv :=
  ⟨![1, 0, -1, 0], by ext <;> simp [x3inv, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

theorem x3_mem_gammaStar :
    glOf x3 (by rw [det_x3]; norm_num) ∈ PkgI1.GammaStar := by
  refine ⟨x3, ⟨x3inv, ?_, ?_, fun z hz => ⟨inO_mul (inO_mul inO_x3 hz) inO_x3inv,
    inO_mul (inO_mul inO_x3inv hz) inO_x3⟩⟩, rfl, ?_⟩
  · ext <;> simp [x3, x3inv] <;> norm_num
  · ext <;> simp [x3, x3inv] <;> norm_num
  · rw [coe_glOf, det_x3]; norm_num

/-- **`S8OrderCM3` from the holomorphy of the theta constants and `S8WeightExact` (proved).** -/
theorem s8OrderCM3_of (hT : ThetaOmegaAnalytic) (h : S8WeightExact) : S8OrderCM3 := by
  have hGa := G8_analytic hT
  set g := glOf x3 (by rw [det_x3]; norm_num) with hg
  have hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![1/2, -3/2; 1/2, 1/2] := by
    rw [hg, coe_glOf, iota_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [x3] <;> norm_num
  have hdetg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by rw [hg, coe_glOf, det_x3]
  set dz : ℂ → ℂ := fun z => z / 2 + 1 / 2 with hdz
  set mz : ℂ → ℂ := fun z => (z / 2 - 3 / 2) / (z / 2 + 1 / 2) with hmz
  have hden : ∀ z : UpperHalfPlane, denom g z = dz z := by
    intro z; simp only [UpperHalfPlane.denom, hgm, hdz]; simp; ring
  have hsmul : ∀ z : UpperHalfPlane, ((g • z : UpperHalfPlane) : ℂ) = mz z := by
    intro z
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdetg]; norm_num)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hgm, hmz]
    simp
    ring_nf
  -- the functional equation on `ℍ`
  have hFE : ∀ z : ℂ, 0 < z.im → G8 (mz z) = dz z ^ 8 * G8 z := by
    intro z hz
    have e := h g x3_mem_gammaStar ⟨z, hz⟩
    rw [hsmul, hden, hdetg] at e
    simpa using e
  set τ₃ : ℂ := (tau3 : ℂ) with hτ₃
  have hτ₃U : τ₃ ∈ U := tau3.im_pos
  have hτ₃im : (0 : ℝ) < τ₃.im := tau3.im_pos
  have hmτ : mz τ₃ = τ₃ := by
    have := hsmul tau3
    rw [cm3_tau3] at this
    exact this.symm
  set w : ℂ := dz τ₃ with hw
  have h3 : (√3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hwv : w = 1 / 2 + (√3 : ℂ) / 2 * I := by
    simp only [hw, hdz, hτ₃, tau3]; push_cast; ring
  have hw3 : w ^ 3 = -1 := by
    rw [hwv]
    linear_combination ((√3 : ℂ) ^ 2 * (I * √3 + 3) / 8) * I_sq + (-(I * √3 + 3) / 8) * h3
  have hw2 : w ^ 2 = -1 / 2 + (√3 : ℂ) / 2 * I := by
    rw [hwv]; linear_combination ((√3 : ℂ) ^ 2 / 4) * I_sq + (-1 / 4 : ℂ) * h3
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0] at hw3; norm_num at hw3
  -- `G8(τ₃) = 0`
  have hG0 : G8 τ₃ = 0 := by
    have e := hFE τ₃ hτ₃im
    rw [hmτ] at e
    have hw8 : w ^ 8 = w ^ 2 := by
      rw [show w ^ 8 = w ^ 2 * (w ^ 3) ^ 2 by ring, hw3]; ring
    have hne : w ^ 8 - 1 ≠ 0 := by
      rw [hw8, hw2]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    have : (w ^ 8 - 1) * G8 τ₃ = 0 := by
      simp only [hw] at e ⊢; linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left hne
  -- `G8'(τ₃) = 0`
  have hGd : DifferentiableAt ℂ G8 τ₃ := (hGa τ₃ hτ₃U).differentiableAt
  have hdzd : ∀ z, HasDerivAt dz (1 / 2) z := by
    intro z
    show HasDerivAt (fun z : ℂ => z / 2 + 1 / 2) (1 / 2) z
    exact ((hasDerivAt_id' z).div_const 2).add_const (1 / 2 : ℂ)
  have hnumd : HasDerivAt (fun z : ℂ => z / 2 - 3 / 2) (1 / 2) τ₃ := by
    exact ((hasDerivAt_id' τ₃).div_const 2).sub_const (3 / 2 : ℂ)
  have hmzd : HasDerivAt mz ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) / dz τ₃ ^ 2) τ₃ :=
    hnumd.div (hdzd τ₃) hw0
  have hL : HasDerivAt (G8 ∘ mz) (deriv G8 τ₃ * ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) /
      dz τ₃ ^ 2)) τ₃ := by
    have hG' : HasDerivAt G8 (deriv G8 τ₃) (mz τ₃) := by rw [hmτ]; exact hGd.hasDerivAt
    exact hG'.comp τ₃ hmzd
  have hR : HasDerivAt (fun z => dz z ^ 8 * G8 z)
      ((8 : ℕ) * dz τ₃ ^ (8 - 1) * (1 / 2) * G8 τ₃ + dz τ₃ ^ 8 * deriv G8 τ₃) τ₃ :=
    ((hdzd τ₃).pow 8).mul hGd.hasDerivAt
  have hEq : (G8 ∘ mz) =ᶠ[𝓝 τ₃] (fun z => dz z ^ 8 * G8 z) := by
    filter_upwards [isOpen_U.mem_nhds hτ₃U] with z hz
    exact hFE z hz
  have hL' := hL.congr_of_eventuallyEq hEq.symm
  have huniq := hL'.unique hR
  rw [hG0, mul_zero, zero_add] at huniq
  have hnum1 : (1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) = 1 := by simp only [hdz]; ring
  rw [hnum1] at huniq
  have hD0 : deriv G8 τ₃ = 0 := by
    have hw10 : w ^ 10 = -w := by
      rw [show w ^ 10 = w * (w ^ 3) ^ 3 by ring, hw3]; ring
    have e2 : deriv G8 τ₃ * (1 - w ^ 10) = 0 := by
      have : deriv G8 τ₃ = w ^ 10 * deriv G8 τ₃ := by
        have hw2ne : dz τ₃ ^ 2 ≠ 0 := pow_ne_zero 2 hw0
        calc deriv G8 τ₃
            = deriv G8 τ₃ * (1 / dz τ₃ ^ 2) * dz τ₃ ^ 2 := by
              rw [mul_assoc, one_div_mul_cancel hw2ne, mul_one]
          _ = dz τ₃ ^ 8 * deriv G8 τ₃ * dz τ₃ ^ 2 := by rw [huniq]
          _ = w ^ 10 * deriv G8 τ₃ := by simp only [hw]; ring
      linear_combination this
    rw [hw10] at e2
    have hne : (1 - -w) ≠ 0 := by
      rw [hwv]; intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    exact (mul_eq_zero.mp e2).resolve_right hne
  -- order at least 2
  show 2 ≤ analyticOrderAt G8 τ₃
  by_contra hlt
  push Not at hlt
  have hA := hGa τ₃ hτ₃U
  have hne0 : analyticOrderAt G8 τ₃ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hA, hG0⟩
  have h1 : analyticOrderAt G8 τ₃ = 1 := by
    have h1' : analyticOrderAt G8 τ₃ ≤ 1 := by simpa using hlt
    exact le_antisymm h1' (Order.one_le_iff_ne_zero.mpr hne0)
  obtain ⟨φ, hφ, hφ0, hφe⟩ := (hA.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  have hd1 : HasDerivAt (fun z => (z - τ₃) ^ 1 • φ z) (φ τ₃) τ₃ := by
    have := ((hasDerivAt_id' τ₃).sub_const τ₃).mul hφ.differentiableAt.hasDerivAt
    simp only [pow_one, smul_eq_mul]
    convert this using 1
    ring
  have hd2 : HasDerivAt G8 (φ τ₃) τ₃ := hd1.congr_of_eventuallyEq hφe
  exact hφ0 (hd2.deriv.symm.trans hD0)

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8WeightExact` and `ValenceBoundGammaStar` (proved).** -/
theorem qmDenZeroCM3_of'' (hS : S8Nonzero) (hW : S8WeightExact) (hV : ValenceBoundGammaStar) :
    QMDenZeroCM3 :=
  qmDenZeroCM3_of' hS (s8Weight8_of hW) (s8OrderCM3_of thetaOmegaAnalytic_proof hW) hV

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.s8Weight8_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.s8OrderCM3_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of''
