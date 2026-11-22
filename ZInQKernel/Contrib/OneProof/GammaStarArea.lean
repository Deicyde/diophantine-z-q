import ZInQKernel.Contrib.OneProof.H.TailZ24

/-! # `Γ*` is a cocompact Fuchsian group of covolume `π/6` (task gt-gamma)

`HDec.GammaStarArea.gammaStarCocompactArea_proof : HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea`, with no
hypotheses. This makes the published leaf `shimizuCovolumeO1` (Shimizu's covolume `2π/3` of `ι(𝒪¹)`) unnecessary:
its only use is `gammaStarFromO1_proof' l.shimizuCovolumeO1` (TailZ4 L237, L249, inside
`qmHauptmodulBase3_of_shimizu`); `valenceFormulaGammaStar_noShimizu` and `qmHauptmodulBase3_noShimizu` below are
the rerouted rows. Moreover the leaf itself is proved: `shimizuCovolumeO1_proof :
HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` (fundamental domain `⋃ᵢ rᵢ⁻¹ T` of `Γ¹ = ι(𝒪¹)`, area `2π/3`), so
the fold can simply fill the bundle field. Report: `docs/research/gt-gamma.md`.

The proof (all of it here, standard axioms only):
* `p = i√3` (`tau3`, the order-6 point). For `g` with matrix `ι(y)`, `nrd y > 0`:
  `F(g w) = F(w) + Φ_y(w)/(nrd(y) Im w)` where `F(w) = |w − p|²/Im w` (`cosh d(w, p) = 1 + F/(2√3)`) and
  `Φ_y = P(U + 6) + 2√2 (RU − SX)`, `U = |w|² − 3`, `X = 6 Re w` (`Fp_smul`). In particular
  `cosh d(p, ι(y)p) = 1 + P/nrd y` with `P = 4a₁² + 12a₃²`, a positive definite bound on `y ∈ 𝒪` together with
  `nrd y ≤ 6`, so only finitely many Möbius maps of `Γ*` move `p` a bounded distance (`finite_mob`): proper
  discontinuity and the existence of an orbit point nearest `p` (`exists_min`). Every `γ ∈ Γ*` acts as `ι(y)`
  with `y ∈ 𝒪`, `nrd y ∈ {1, 2, 3, 6}` (`cover_y`, from the chain's `cover_mob`, i.e. `gammaStarGen_proof`).
* `T = {X ≤ U, −X ≤ U, U ≤ 6 + 6√2}` is the geodesic triangle with vertices `i√3`, `±(1 + √2) + i(2 + √2)`.
  Covering (`cover_T`): rotate the nearest orbit point into the cone `U ≥ |X|` by the stabilizer of `p`
  (`cone_step`), then compare with `σ = ι(μ)`, `μ = 2j + ij` (`|w|² ≤ 9 + 6√2`).
* Dirichlet property (`dirichlet`): `Φ_y ≥ 0` on `T` for every `y`; `Φ_y` is affine in `(U, X)`, so it suffices
  at the three vertices, where it is the integer inequality `intV` (Cauchy–Schwarz when `A₁² + 3A₃² ≥ 4N`, a
  finite enumeration otherwise).
* A.e. disjointness (`disjoint_T`): on `T ∩ γ⁻¹T` both Dirichlet inequalities are equalities, so `Φ_y = 0`, a
  circle or line orthogonal to `ℝ` (null), unless `y` fixes `p`, where the cone argument leaves two rays.
* Area (`volume_T`): Tonelli on `dx dy/y²`, `∫ dy/y²` and the arcsine antiderivatives:
  `2 (π/3 − π/4) = π/6` (`AreaCalc.area_TC`).
-/

set_option linter.all false


noncomputable section

namespace HDec.GammaStarArea

open LeafQCheck LeafQCheck.QMglue PkgI1
open UpperHalfPlane (num denom denom_ne_zero)
open HSyn.G0Split.FibreQM.PeriodGlue (x4 x6)

local notation "p0" => HSyn.G0Split.FibreQM.PeriodMap.tau3


theorem p0_coe : ((p0 : UpperHalfPlane) : ℂ) = (√3 : ℂ) * Complex.I := rfl

theorem p0_im : (p0 : UpperHalfPlane).im = √3 := by
  show ((p0 : UpperHalfPlane) : ℂ).im = √3
  rw [p0_coe]; simp

theorem p0_re : (p0 : UpperHalfPlane).re = 0 := by
  show ((p0 : UpperHalfPlane) : ℂ).re = 0
  rw [p0_coe]; simp

/-- `F(z) = |z - p|² / Im z`, `p = i√3`; `cosh d(z, p) = 1 + F(z)/(2√3)`. -/
def Fp (z : UpperHalfPlane) : ℝ := Complex.normSq ((z : ℂ) - (p0 : ℂ)) / z.im

theorem sqrt3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)

theorem cosh_dist_p0 (z : UpperHalfPlane) : Real.cosh (dist z p0) = 1 + Fp z / (2 * √3) := by
  rw [UpperHalfPlane.cosh_dist, p0_im, Fp, Complex.dist_eq, Complex.sq_norm]
  have := z.im_pos
  have := sqrt3_pos
  field_simp

theorem dist_le_iff (z w : UpperHalfPlane) : dist z p0 ≤ dist w p0 ↔ Fp z ≤ Fp w := by
  have h := Real.cosh_le_cosh (x := dist z p0) (y := dist w p0)
  rw [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at h
  rw [← h, cosh_dist_p0, cosh_dist_p0, add_le_add_iff_left]
  exact div_le_div_iff_of_pos_right (by have := sqrt3_pos; positivity)

theorem dist_eq_iff (z w : UpperHalfPlane) : dist z p0 = dist w p0 ↔ Fp z = Fp w := by
  constructor
  · intro h; exact le_antisymm ((dist_le_iff z w).1 h.le) ((dist_le_iff w z).1 h.ge)
  · intro h; exact le_antisymm ((dist_le_iff z w).2 h.le) ((dist_le_iff w z).2 h.ge)

/-! ## The action of `ι(y)` -/

/-- `P = 4a₁² + 12a₃²`, `R = a₀a₁ − 3a₂a₃`, `S = a₀a₃ + a₁a₂` for `y = a₀ + a₁i + a₂j + a₃k`. -/
def Pq (y : B) : ℝ := 4 * (y.imI : ℝ) ^ 2 + 12 * (y.imK : ℝ) ^ 2
def Rq (y : B) : ℝ := (y.re : ℝ) * y.imI - 3 * (y.imJ : ℝ) * y.imK
def Sq (y : B) : ℝ := (y.re : ℝ) * y.imK + (y.imI : ℝ) * y.imJ

/-- `U = |w|² − 3`, `X = 6 Re w`. -/
def Uq (w : UpperHalfPlane) : ℝ := Complex.normSq (w : ℂ) - 3
def Xq (w : UpperHalfPlane) : ℝ := 6 * w.re

/-- `Φ_y(w) = P(U + 6) + 2√2 (RU − SX)`: `F(ι(y) w) = F(w) + Φ_y(w)/(nrd(y) Im w)`. -/
def Phi (y : B) (w : UpperHalfPlane) : ℝ :=
  Pq y * (Uq w + 6) + 2 * √2 * (Rq y * Uq w - Sq y * Xq w)

theorem det_pos_of {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) : 0 < g.det.val := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg, det_iota_eq]; exact_mod_cast hn

theorem Fp_smul {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (w : UpperHalfPlane) :
    Fp (g • w) = Fp w + Phi y w / ((nrd y : ℝ) * w.im) := by
  have hdet := det_pos_of hg hn
  have hdet' : g.det.val = (nrd y : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, det_iota_eq]
  have hD := denom_ne_zero g w
  have hDn : Complex.normSq (denom g w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have hc := UpperHalfPlane.coe_smul_of_det_pos hdet w
  have him := UpperHalfPlane.im_smul_eq_div_normSq g w
  rw [abs_of_pos hdet, hdet'] at him
  have hsub : ((g • w : UpperHalfPlane) : ℂ) - (p0 : ℂ) =
      (num g w - (p0 : ℂ) * denom g w) / denom g w := by
    rw [hc]; field_simp
  have hwim := w.im_pos
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hn
  have key : Complex.normSq (num g w - (p0 : ℂ) * denom g w) =
      (nrd y : ℝ) * Complex.normSq ((w : ℂ) - (p0 : ℂ)) + Phi y w := by
    have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (y.re : ℝ) + y.imI * √2 := by
      rw [hg, iota_apply]; simp
    have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -3 * (y.imJ : ℝ) - 3 * √2 * y.imK := by
      rw [hg, iota_apply]; simp
    have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (y.imJ : ℝ) - √2 * y.imK := by
      rw [hg, iota_apply]; simp
    have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (y.re : ℝ) - y.imI * √2 := by
      rw [hg, iota_apply]; simp
    simp only [num, denom, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, p0_coe,
      Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, e00, e01, e10, e11]
    simp only [Phi, Pq, Rq, Sq, Uq, Xq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, nrd]
    push_cast
    have hs : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have ht : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    set s := √2
    set t := √3
    set x := w.re
    set yy := w.im
    set a0 := (y.re : ℝ)
    set a1 := (y.imI : ℝ)
    set a2 := (y.imJ : ℝ)
    set a3 := (y.imK : ℝ)
    linear_combination (9*a3^2 + a1^2*t^2 + 6*yy*a3^2*t + 2*yy*a1^2*t + yy^2*a3^2*t^2 + yy^2*a1^2 +
      (-6)*x*a1*a3 + 2*x*a1*a3*t^2 + x^2*a3^2*t^2 + x^2*a1^2) * hs +
      (6*a3^2 + (-3)*a2^2 + 4*a1^2 + (-2)*a0*a1*s + 2*yy^2*a3^2 + (-2)*yy^2*a2*a3*s + yy^2*a2^2 +
      4*x*a1*a3 + (-2)*x*a1*a2*s + (-2)*x*a0*a3*s + 2*x*a0*a2 + 2*x^2*a3^2 + (-2)*x^2*a2*a3*s +
      x^2*a2^2) * ht
  unfold Fp
  rw [hsub, Complex.normSq_div, key, him]
  field_simp


/-! ## Isometries -/

/-- A matrix of positive determinant acts on `ℍ` by an isometry. -/
theorem dist_smul_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z w : UpperHalfPlane) :
    dist (g • z) (g • w) = dist z w := by
  set c : ℝ := √(g.det.val) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 hg
  have hcsq : c ^ 2 = g.det.val := Real.sq_sqrt hg.le
  let g' : Matrix.SpecialLinearGroup (Fin 2) ℝ := ⟨c⁻¹ • (g : Matrix (Fin 2) (Fin 2) ℝ), by
    rw [Matrix.det_smul, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply, ← hcsq]
    field_simp⟩
  have key : ∀ u : UpperHalfPlane, g' • u = g • u := by
    intro u
    have e : Matrix.SpecialLinearGroup.mapGL ℝ g' =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c⁻¹ (inv_ne_zero hc0.ne')) * g := by
      ext i j
      rw [Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.GeneralLinearGroup.coe_scalar]
      simp [g', Matrix.scalar_apply, Matrix.diagonal_mul]
      rfl
    rw [MulAction.compHom_smul_def, e, mul_smul, UpperHalfPlane.glScalar_smul]
  rw [← key, ← key, dist_smul]

/-! ## `cosh d(p, ι(y) p) = 1 + P/nrd` -/

theorem Fp_p0 : Fp p0 = 0 := by simp [Fp]

theorem Uq_p0 : Uq p0 = 0 := by
  simp only [Uq, p0_coe, Complex.normSq_apply]; simp
theorem Xq_p0 : Xq p0 = 0 := by simp [Xq, p0_re]

theorem cosh_dist_smul_p0 {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) : Real.cosh (dist (g • p0) p0) = 1 + Pq y / nrd y := by
  rw [cosh_dist_p0, Fp_smul hg hn, Fp_p0, Phi, Uq_p0, Xq_p0, p0_im]
  have := sqrt3_pos
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hn
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  field_simp
  linear_combination (-2 : ℝ) * Pq y * h3

theorem Pq_nonneg (y : B) : 0 ≤ Pq y := by unfold Pq; positivity

/-! ## Elements of `Γ*` as `ι(y)` with `y ∈ 𝒪`, `nrd y ∈ {1, 2, 3, 6}` -/

theorem inO_rep (i : Fin 4) : InO (rep i) := by
  have h1 : InO (1 : B) := (inO_iff _).2 ⟨1, 0, 0, 0, by ext <;> norm_num⟩
  have h4 : InO x4 := (inO_iff _).2 ⟨0, 1, 2, 0, by ext <;> norm_num [x4]⟩
  have h6 : InO x6 := (inO_iff _).2 ⟨-2, 0, 1, 0, by
    ext <;> norm_num [x6]⟩
  fin_cases i
  · simpa [rep] using h1
  · simpa [rep] using h4
  · simpa [rep] using h6
  · simpa [rep] using inO_mul h4 h6

/-- The Möbius map of `γ ∈ Γ*` is that of `ι(y)`, `y ∈ 𝒪`, `nrd y ∈ {1, 2, 3, 6}` (from `cover_mob`). -/
theorem cover_y {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) :
    ∃ y : B, InO y ∧ (nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) ∧
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y ∧ ∀ z : UpperHalfPlane, γ • z = g • z := by
  obtain ⟨i, h, hh, hz⟩ := cover_mob hγ
  obtain ⟨u, hu, hhu, hnu⟩ := gamma1_iff.1 hh
  refine ⟨rep i * u, inO_mul (inO_rep i) hu, ?_, g4 i * h, ?_, fun z => by rw [hz, mul_smul]⟩
  · rw [nrd_mul, hnu, mul_one, nrd_rep]
    fin_cases i <;> simp
  · rw [Units.val_mul, g4_coe, hhu, iota_mul]

theorem nrd_pos_of {y : B} (h : nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) : 0 < nrd y := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

theorem nrd_le_six {y : B} (h : nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) : nrd y ≤ 6 := by
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

theorem isom {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) (z w : UpperHalfPlane) :
    dist (γ • z) (γ • w) = dist z w :=
  dist_smul_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact det_pos_of_mem hγ) z w

/-! ## Finiteness -/

/-- The Möbius map of `ι(y)` (identity if `nrd y = 0`). -/
def mobOf (y : B) : UpperHalfPlane → UpperHalfPlane :=
  fun z => (if h : nrd y ≠ 0 then glOf y h else 1) • z

theorem mobOf_eq {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : nrd y ≠ 0) : (fun z => g • z) = mobOf y := by
  have : g = glOf y hn := by ext1; rw [coe_glOf, hg]
  funext z; simp [mobOf, hn, this]

theorem abs_le_of_sq_le {A : ℤ} {G : ℝ} (h : (A : ℝ) ^ 2 ≤ G) : |A| ≤ ⌈G⌉ := by
  have h1 : (|A| : ℤ) ≤ A ^ 2 := by
    rcases eq_or_ne A 0 with h0 | h0
    · simp [h0]
    · have : 1 ≤ |A| := Int.one_le_abs h0
      calc |A| = |A| * 1 := by ring
        _ ≤ |A| * |A| := by gcongr
        _ = A ^ 2 := by rw [← abs_mul, abs_mul_self, sq]
  have h2 : ((|A| : ℤ) : ℝ) ≤ G := le_trans (by exact_mod_cast h1) h
  exact Int.cast_le.1 (le_trans h2 (Int.le_ceil G))

theorem finite_O (D : ℝ) : {y : B | InO y ∧ nrd y ≤ 6 ∧ Pq y ≤ D}.Finite := by
  set M : ℤ := ⌈4 * D + 24⌉
  let f : ℤ × ℤ × ℤ × ℤ → B := fun v =>
    ⟨(v.1 : ℚ) + (v.2.2.1 : ℚ) / 2, (v.2.1 : ℚ) + (v.2.2.2 : ℚ) / 2, (v.2.2.1 : ℚ) / 2,
      (v.2.2.2 : ℚ) / 2⟩
  refine ((((Set.finite_Icc (-M) M).prod ((Set.finite_Icc (-M) M).prod
    ((Set.finite_Icc (-M) M).prod (Set.finite_Icc (-M) M))))).image f).subset ?_
  rintro y ⟨hy, hn6, hP⟩
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff y).1 hy
  simp only [Pq] at hP
  simp only [nrd] at hn6
  have hn6' : ((n0 : ℝ) + n2 / 2) ^ 2 - 2 * ((n1 : ℝ) + n3 / 2) ^ 2 + 3 * ((n2 : ℝ) / 2) ^ 2 -
      6 * ((n3 : ℝ) / 2) ^ 2 ≤ 6 := by exact_mod_cast hn6
  push_cast at hP
  have b3 : ((n3 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by nlinarith
  have b1 : ((2 * n1 + n3 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by push_cast; nlinarith
  have b2 : ((n2 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by nlinarith
  have b0 : ((2 * n0 + n2 : ℤ) : ℝ) ^ 2 ≤ 4 * D + 24 := by push_cast; nlinarith
  have a3 := abs_le_of_sq_le b3
  have a1 := abs_le_of_sq_le b1
  have a2 := abs_le_of_sq_le b2
  have a0 := abs_le_of_sq_le b0
  refine ⟨(n0, n1, n2, n3), ⟨?_, ?_, ?_, ?_⟩, rfl⟩ <;> simp only [Set.mem_Icc] <;>
    constructor <;> (try rw [abs_le] at a0 a1 a2 a3) <;> omega

/-- Only finitely many Möbius maps of `Γ*` move `p` by at most `C`. -/
theorem finite_mob (C : ℝ) : {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs,
    f = (fun z => γ • z) ∧ dist (γ • p0) p0 ≤ C}.Finite := by
  refine ((finite_O (6 * Real.cosh C)).image mobOf).subset ?_
  rintro f ⟨γ, hγ, rfl, hC⟩
  obtain ⟨y, hy, hn, g, hg, hz⟩ := cover_y hγ
  have hpos := nrd_pos_of hn
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hpos
  have hn6 : (nrd y : ℝ) ≤ 6 := by exact_mod_cast nrd_le_six hn
  refine ⟨y, ⟨hy, nrd_le_six hn, ?_⟩, ?_⟩
  · have h1 := cosh_dist_smul_p0 hg hpos
    rw [← hz] at h1
    have h2 : Real.cosh (dist (γ • p0) p0) ≤ Real.cosh C := by
      rw [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
      exact hC.trans (le_abs_self C)
    have h3 : Pq y / nrd y ≤ Real.cosh C - 1 := by linarith
    have h4 : Pq y ≤ (Real.cosh C - 1) * nrd y := (div_le_iff₀ hnr).1 h3
    have h5 : 1 ≤ Real.cosh C := Real.one_le_cosh C
    nlinarith
  · rw [← mobOf_eq hg hpos.ne']; funext z; exact (hz z).symm

theorem properlyDiscontinuous (K : Set UpperHalfPlane) (hK : IsCompact K) :
    {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs, f = (fun z => γ • z) ∧
      (f '' K ∩ K).Nonempty}.Finite := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall p0
  refine (finite_mob (r + r)).subset ?_
  rintro f ⟨γ, hγ, rfl, ⟨_, ⟨k, hk, rfl⟩, hk'⟩⟩
  refine ⟨γ, hγ, rfl, ?_⟩
  have h1 := hr hk
  have h2 := hr hk'
  rw [Metric.mem_closedBall] at h1 h2
  calc dist (γ • p0) p0 ≤ dist (γ • p0) (γ • k) + dist (γ • k) p0 := dist_triangle _ _ _
    _ = dist p0 k + dist (γ • k) p0 := by rw [isom hγ]
    _ ≤ r + r := by rw [dist_comm]; exact add_le_add h1 h2

/-- A point of the orbit of `z` closest to `p`. -/
theorem exists_min (z : UpperHalfPlane) :
    ∃ γ₀ ∈ Γs, ∀ γ ∈ Γs, dist (γ₀ • z) p0 ≤ dist (γ • z) p0 := by
  set S := {f : UpperHalfPlane → UpperHalfPlane | ∃ γ ∈ Γs, f = (fun z => γ • z) ∧
    dist (f z) p0 ≤ dist z p0} with hS
  have hfin : S.Finite := by
    refine (finite_mob (dist z p0 + dist z p0)).subset ?_
    rintro f ⟨γ, hγ, rfl, hd⟩
    refine ⟨γ, hγ, rfl, ?_⟩
    calc dist (γ • p0) p0 ≤ dist (γ • p0) (γ • z) + dist (γ • z) p0 := dist_triangle _ _ _
      _ = dist p0 z + dist (γ • z) p0 := by rw [isom hγ]
      _ ≤ dist z p0 + dist z p0 := by rw [dist_comm p0 z]; exact add_le_add le_rfl hd
  have hne : S.Nonempty := ⟨fun z => (1 : GL (Fin 2) ℝ) • z, 1, gs_one, rfl, by simp⟩
  obtain ⟨f, ⟨γ₀, hγ₀, rfl, hd₀⟩, hmin⟩ := Set.exists_min_image S (fun f => dist (f z) p0) hfin hne
  refine ⟨γ₀, hγ₀, fun γ hγ => ?_⟩
  by_cases hγz : dist (γ • z) p0 ≤ dist z p0
  · exact hmin _ ⟨γ, hγ, rfl, hγz⟩
  · push Not at hγz; exact hd₀.trans hγz.le


/-! ## The stabilizer of `p` acts on `(X, U)` linearly -/

theorem coe_smul_eq {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) (w : UpperHalfPlane) :
    ((g • w : UpperHalfPlane) : ℂ) = num g w / denom g w :=
  UpperHalfPlane.coe_smul_of_det_pos hdet w

/-- For `y = a₀ + a₂ j`: `|cw+d|² U(ι(y)w) = αU − 2βX`, `|cw+d|² X(ι(y)w) = αX + 6βU`, `α = a₀² − 3a₂²`,
`β = a₀a₂`. -/
theorem cone_smul {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) :
    Complex.normSq (denom g w) * Uq (g • w) =
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w ∧
      Complex.normSq (denom g w) * Xq (g • w) =
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w := by
  have hdet := det_pos_of hg hn
  have hD := denom_ne_zero g w
  have hDn : Complex.normSq (denom g w) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -3 * (y.imJ : ℝ) := by rw [hg, iota_apply]; simp [hK]
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = (y.imJ : ℝ) := by rw [hg, iota_apply]; simp [hK]
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  have hU : Uq (g • w) = Complex.normSq (num g w) / Complex.normSq (denom g w) - 3 := by
    rw [Uq, coe_smul_eq hdet, Complex.normSq_div]
  have hX : Xq (g • w) = 6 * (((num g w).re * (denom g w).re + (num g w).im * (denom g w).im) /
      Complex.normSq (denom g w)) := by
    rw [Xq, ← UpperHalfPlane.coe_re, coe_smul_eq hdet, Complex.div_re]; ring
  rw [hU, hX]
  constructor
  · field_simp
    simp only [num, denom, Uq, Xq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      e00, e01, e10, e11]
    ring
  · field_simp
    simp only [num, denom, Uq, Xq, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
      e00, e01, e10, e11]
    ring

theorem Phi_stab {y : B} (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) : Phi y w = 0 := by
  simp [Phi, Pq, Rq, Sq, hI, hK]

theorem dist_stab {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane) :
    dist (g • w) p0 = dist w p0 := by
  rw [dist_eq_iff, Fp_smul hg hn, Phi_stab hI hK]; simp

/-- The cone step for one stabilizer element. -/
theorem cone_of {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) (w : UpperHalfPlane)
    (h1 : ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w ≤
      ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w)
    (h2 : -(((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Xq w + 6 * ((y.re : ℝ) * y.imJ) * Uq w) ≤
      ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * Uq w - 2 * ((y.re : ℝ) * y.imJ) * Xq w) :
    Xq (g • w) ≤ Uq (g • w) ∧ -Xq (g • w) ≤ Uq (g • w) ∧ dist (g • w) p0 = dist w p0 := by
  obtain ⟨hu, hx⟩ := cone_smul hg hn hI hK w
  have hm : 0 < Complex.normSq (denom g w) := Complex.normSq_pos.2 (denom_ne_zero g w)
  refine ⟨?_, ?_, dist_stab hg hn hI hK w⟩
  · by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h hm
    linarith
  · by_contra h; push Not at h
    have := mul_lt_mul_of_pos_left h hm
    linarith

/-! ### Six elements of the stabilizer of `p` in `Γ*` -/

/-- `u₊ = (1 + j)/2`, `u₋ = (1 − j)/2` (norm one). -/
def uP : B := ⟨1 / 2, 0, 1 / 2, 0⟩
def uM : B := ⟨1 / 2, 0, -1 / 2, 0⟩

theorem nrd_uP : nrd uP = 1 := by norm_num [nrd, uP]
theorem nrd_uM : nrd uM = 1 := by norm_num [nrd, uM]
theorem inO_uP : InO uP := (inO_iff _).2 ⟨0, 0, 1, 0, by ext <;> norm_num [uP]⟩
theorem inO_uM : InO uM := (inO_iff _).2 ⟨1, 0, -1, 0, by ext <;> norm_num [uM]⟩

/-- A norm-one element of `𝒪` gives an element of `Γ*`. -/
theorem mem_of_norm_one {u : B} (hu : InO u) (hn : nrd u = 1) :
    glOf u (by rw [hn]; norm_num) ∈ Γs :=
  gamma1_sub (gamma1_iff.2 ⟨u, hu, coe_glOf _ _, hn⟩)

theorem x6_uM : x6 * uM = (⟨0, 0, 1, 0⟩ : B) := by
  ext <;> norm_num [x6, uM]

theorem rep2 : rep 2 = x6 := by simp [rep]
theorem repi2 : repi 2 = x6i := by simp [repi]

theorem cone_step (w : UpperHalfPlane) : ∃ γ ∈ Γs,
    Xq (γ • w) ≤ Uq (γ • w) ∧ -Xq (γ • w) ≤ Uq (γ • w) ∧ dist (γ • w) p0 = dist w p0 := by
  set U := Uq w
  set X := Xq w
  have h6 : (0 : ℚ) < nrd x6 := by norm_num [nrd, x6]
  have h6i : (0 : ℚ) < nrd x6i := by norm_num [nrd, x6i]
  have hx6 : ((g4 2 : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = iota x6 := by rw [g4_coe, rep2]
  have hx6i : (((g4 2)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = iota x6i := by
    rw [inv_coe (g4_coe 2) (rep_repi 2), repi2]
  rcases le_total X U with hXU | hUX <;> rcases le_total (-X) U with hXU' | hUX'
  · -- cone A
    exact ⟨1, gs_one, by simpa using hXU, by simpa using hXU', by simp⟩
  · -- `U ≤ -X`, `X ≤ U`: split by the sign of `U`
    rcases le_total 0 U with hU | hU
    · -- cone B: `x₆⁻¹`
      refine ⟨(g4 2)⁻¹, gs_inv (g4_mem 2), cone_of hx6i h6i (by simp [x6i]) (by simp [x6i]) w ?_ ?_⟩ <;>
        norm_num [x6i] <;> linarith
    · -- cone C: `u₊`
      refine ⟨_, mem_of_norm_one inO_uP nrd_uP,
        cone_of (coe_glOf _ _) (by rw [nrd_uP]; norm_num) (by simp [uP]) (by simp [uP]) w ?_ ?_⟩ <;>
        norm_num [uP] <;> linarith
  · rcases le_total 0 U with hU | hU
    · -- cone F: `x₆`
      refine ⟨g4 2, g4_mem 2, cone_of hx6 h6 (by simp [x6]) (by simp [x6]) w ?_ ?_⟩ <;>
        norm_num [x6] <;> linarith
    · -- cone E: `u₋`
      refine ⟨_, mem_of_norm_one inO_uM nrd_uM,
        cone_of (coe_glOf _ _) (by rw [nrd_uM]; norm_num) (by simp [uM]) (by simp [uM]) w ?_ ?_⟩ <;>
        norm_num [uM] <;> linarith
  · -- cone D: `j = x₆ u₋`
    have hj : ((g4 2 * glOf uM (by rw [nrd_uM]; norm_num) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        iota (⟨0, 0, 1, 0⟩ : B) := by
      rw [Units.val_mul, hx6, coe_glOf, ← iota_mul, x6_uM]
    refine ⟨_, gs_mul (g4_mem 2) (mem_of_norm_one inO_uM nrd_uM),
      cone_of hj (by norm_num [nrd]) rfl rfl w ?_ ?_⟩ <;> norm_num <;> linarith

/-! ## `ι(μ)`, `μ = 2j + ij`, lies in `Γ*` -/

theorem muInv_mul_mu : PkgI1.muInv * PkgI1.mu = 1 := by
  ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> norm_num

theorem conj_mu : ∀ w, InO w → InO (PkgI1.mu * w * PkgI1.muInv) ∧ InO (PkgI1.muInv * w * PkgI1.mu) := by
  intro w hw
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  constructor
  · refine (inO_iff _).2 ⟨n0 - n2 + 2 * n3, -n1 - n2 + n3, 3 * n2 - 4 * n3, 2 * n2 - 3 * n3, ?_⟩
    ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> ring
  · refine (inO_iff _).2 ⟨n0 - n2 + 2 * n3, -n1 - n2 + n3, 3 * n2 - 4 * n3, 2 * n2 - 3 * n3, ?_⟩
    ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> ring

theorem nrd_mu : nrd PkgI1.mu = 6 := by norm_num [nrd, PkgI1.mu]

/-- `σ = ι(μ)`: the half-turn about `i√(9 + 6√2)`. -/
def sigma : GL (Fin 2) ℝ := glOf PkgI1.mu (by rw [nrd_mu]; norm_num)

theorem sigma_mem : sigma ∈ Γs :=
  ⟨PkgI1.mu, ⟨PkgI1.muInv, PkgI1.mu_mul_muInv, muInv_mul_mu, conj_mu⟩, coe_glOf _ _, by
    rw [sigma, coe_glOf, det_iota_eq, nrd_mu]; norm_num⟩

/-! ## The fundamental triangle and the covering -/

/-- The triangle `T` with vertices `i√3`, `±(1+√2) + i(2+√2)`. -/
def Tset : Set UpperHalfPlane := {w | Xq w ≤ Uq w ∧ -Xq w ≤ Uq w ∧ Uq w ≤ 6 + 6 * √2}

theorem cover_T (z : UpperHalfPlane) : ∃ γ ∈ Γs, γ • z ∈ Tset := by
  obtain ⟨γ₀, hγ₀, hmin⟩ := exists_min z
  obtain ⟨g, hg, h1, h2, hd⟩ := cone_step (γ₀ • z)
  refine ⟨g * γ₀, gs_mul hg hγ₀, ?_⟩
  set w := (g * γ₀) • z with hw
  have hw' : w = g • γ₀ • z := mul_smul _ _ _
  rw [← hw'] at h1 h2 hd
  refine ⟨h1, h2, ?_⟩
  have hle : dist w p0 ≤ dist (sigma • w) p0 := by
    rw [hd, hw, ← mul_smul]
    exact hmin _ (gs_mul sigma_mem (gs_mul hg hγ₀))
  rw [dist_le_iff, Fp_smul (g := sigma) (y := PkgI1.mu) (coe_glOf _ _) (by rw [nrd_mu]; norm_num)] at hle
  have hpos : 0 < ((nrd PkgI1.mu : ℚ) : ℝ) * w.im := by
    rw [nrd_mu]; have := w.im_pos; positivity
  have hPhi : 0 ≤ Phi PkgI1.mu w := by
    by_contra h; push Not at h
    have := div_neg_of_neg_of_pos h hpos
    linarith
  simp only [Phi, Pq, Rq, Sq, PkgI1.mu] at hPhi
  norm_num at hPhi
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs1 : 1 < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith


/-! ## The Dirichlet property of `T` -/

theorem no_sq3 (a b k : ℤ) (h : a ^ 2 + 3 * b ^ 2 = 3 * k + 2) : False := by
  have h' := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at h'
  generalize (a : ZMod 3) = x at h'
  generalize (b : ZMod 3) = y at h'
  generalize (k : ZMod 3) = z at h'
  revert x y z
  decide

theorem sq3_16 (a b : ℤ) (h : a ^ 2 + 3 * b ^ 2 = 16) :
    ((a = 4 ∨ a = -4) ∧ b = 0) ∨ ((a = 2 ∨ a = -2) ∧ (b = 2 ∨ b = -2)) := by
  have ha : -4 ≤ a ∧ a ≤ 4 := by constructor <;> nlinarith
  have hb : -2 ≤ b ∧ b ≤ 2 := by constructor <;> nlinarith
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> revert h <;> norm_num

theorem sq3_48 (a b : ℤ) (h : a ^ 2 + 3 * b ^ 2 = 48) :
    ((a = 6 ∨ a = -6) ∧ (b = 2 ∨ b = -2)) ∨ (a = 0 ∧ (b = 4 ∨ b = -4)) := by
  have ha : -7 ≤ a ∧ a ≤ 7 := by constructor <;> nlinarith
  have hb : -4 ≤ b ∧ b ≤ 4 := by constructor <;> nlinarith
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  interval_cases a <;> interval_cases b <;> revert h <;> norm_num

/-- **The vertex condition** (integers `A_i = 2a_i`): `2P + R' ∓ S' ≥ 0` for every `y ∈ 𝒪` of reduced norm
`1, 2, 3, 6`; Cauchy–Schwarz when `P ≥ 4N`, enumeration otherwise. -/
theorem intV (A0 A1 A2 A3 N : ℤ) (h1 : ∃ m, A1 = 2 * m + A3)
    (hN : A0 ^ 2 - 2 * A1 ^ 2 + 3 * A2 ^ 2 - 6 * A3 ^ 2 = 4 * N)
    (hNv : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 6) :
    0 ≤ 2 * (A1 ^ 2 + 3 * A3 ^ 2) + (A0 * A1 - 3 * A2 * A3) - (A0 * A3 + A1 * A2) ∧
      0 ≤ 2 * (A1 ^ 2 + 3 * A3 ^ 2) + (A0 * A1 - 3 * A2 * A3) + (A0 * A3 + A1 * A2) := by
  have hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 4 * N + 2 * (A1 ^ 2 + 3 * A3 ^ 2) := by linarith
  have hN1 : 1 ≤ N := by omega
  have hN6 : N ≤ 6 := by omega
  by_cases hP : 4 * N ≤ A1 ^ 2 + 3 * A3 ^ 2
  · set P := A1 ^ 2 + 3 * A3 ^ 2 with hPdef
    set R := A0 * A1 - 3 * A2 * A3
    set S := A0 * A3 + A1 * A2
    have hP0 : 0 ≤ P := by positivity
    have hRS : R ^ 2 + 3 * S ^ 2 = (A0 ^ 2 + 3 * A2 ^ 2) * P := by ring
    have hb : (A0 ^ 2 + 3 * A2 ^ 2) * P ≤ 3 * P ^ 2 := by rw [hnorm]; nlinarith
    have hT1 : 3 * (R - S) ^ 2 ≤ 4 * (R ^ 2 + 3 * S ^ 2) := by nlinarith [sq_nonneg (R + 3 * S)]
    have hT2 : 3 * (R + S) ^ 2 ≤ 4 * (R ^ 2 + 3 * S ^ 2) := by nlinarith [sq_nonneg (R - 3 * S)]
    constructor
    · by_contra h; push Not at h
      nlinarith
    · by_contra h; push Not at h
      nlinarith
  · push Not at hP
    obtain ⟨m1, hm1⟩ := h1
    have hA1 : -4 ≤ A1 ∧ A1 ≤ 4 := by constructor <;> nlinarith
    have hA3 : -2 ≤ A3 ∧ A3 ≤ 2 := by constructor <;> nlinarith
    obtain ⟨hA1l, hA1u⟩ := hA1
    obtain ⟨hA3l, hA3u⟩ := hA3
    rcases hNv with rfl | rfl | rfl | rfl <;> interval_cases A1 <;> interval_cases A3 <;>
      (try norm_num at hP) <;> (try norm_num at hnorm) <;> (try norm_num) <;> (try omega) <;>
      first
      | (guard_hyp hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 20; exact (no_sq3 A0 A2 6 (by linarith)).elim)
      | (guard_hyp hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 32; exact (no_sq3 A0 A2 10 (by linarith)).elim)
      | (guard_hyp hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 56; exact (no_sq3 A0 A2 18 (by linarith)).elim)
      | (guard_hyp hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 16;
          rcases sq3_16 A0 A2 hnorm with ⟨h | h, h'⟩ | ⟨h | h, h' | h'⟩ <;> subst h <;> subst h' <;>
          norm_num)
      | (guard_hyp hnorm : A0 ^ 2 + 3 * A2 ^ 2 = 48;
          rcases sq3_48 A0 A2 hnorm with ⟨h | h, h' | h'⟩ | ⟨h, h' | h'⟩ <;> subst h <;> subst h' <;>
          norm_num)

theorem vertex_cond {y : B} (hy : InO y) (hn : nrd y = 1 ∨ nrd y = 2 ∨ nrd y = 3 ∨ nrd y = 6) :
    0 ≤ Pq y + 2 * (Rq y - Sq y) ∧ 0 ≤ Pq y + 2 * (Rq y + Sq y) := by
  obtain ⟨N, hNq, hNv⟩ : ∃ N : ℤ, nrd y = N ∧ (N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 6) := by
    rcases hn with h | h | h | h
    · exact ⟨1, by rw [h]; norm_num, by norm_num⟩
    · exact ⟨2, by rw [h]; norm_num, by norm_num⟩
    · exact ⟨3, by rw [h]; norm_num, by norm_num⟩
    · exact ⟨6, by rw [h]; norm_num, by norm_num⟩
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff y).1 hy
  have hNq' : ((2 * n0 + n2 : ℤ) : ℚ) ^ 2 - 2 * ((2 * n1 + n3 : ℤ) : ℚ) ^ 2 + 3 * ((n2 : ℤ) : ℚ) ^ 2 -
      6 * ((n3 : ℤ) : ℚ) ^ 2 = 4 * (N : ℚ) := by
    simp only [nrd] at hNq; push_cast; linarith
  have hN : (2 * n0 + n2) ^ 2 - 2 * (2 * n1 + n3) ^ 2 + 3 * n2 ^ 2 - 6 * n3 ^ 2 = 4 * N := by
    exact_mod_cast hNq'
  obtain ⟨v1, v2⟩ := intV (2 * n0 + n2) (2 * n1 + n3) n2 n3 N ⟨n1, rfl⟩ hN hNv
  have w1 : (0 : ℝ) ≤ 2 * (((2 * n1 + n3 : ℤ) : ℝ) ^ 2 + 3 * (n3 : ℝ) ^ 2) +
      (((2 * n0 + n2 : ℤ) : ℝ) * ((2 * n1 + n3 : ℤ) : ℝ) - 3 * (n2 : ℝ) * n3) -
      (((2 * n0 + n2 : ℤ) : ℝ) * n3 + ((2 * n1 + n3 : ℤ) : ℝ) * n2) := by exact_mod_cast v1
  have w2 : (0 : ℝ) ≤ 2 * (((2 * n1 + n3 : ℤ) : ℝ) ^ 2 + 3 * (n3 : ℝ) ^ 2) +
      (((2 * n0 + n2 : ℤ) : ℝ) * ((2 * n1 + n3 : ℤ) : ℝ) - 3 * (n2 : ℝ) * n3) +
      (((2 * n0 + n2 : ℤ) : ℝ) * n3 + ((2 * n1 + n3 : ℤ) : ℝ) * n2) := by exact_mod_cast v2
  push_cast at w1 w2
  simp only [Pq, Rq, Sq]
  push_cast
  constructor <;> nlinarith

theorem sqrt2_sq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)

theorem Phi_nonneg {y : B} (hV1 : 0 ≤ Pq y + 2 * (Rq y - Sq y)) (hV2 : 0 ≤ Pq y + 2 * (Rq y + Sq y))
    {w : UpperHalfPlane} (hw : w ∈ Tset) : 0 ≤ Phi y w := by
  obtain ⟨h1, h2, h3⟩ := hw
  set P := Pq y
  set R := Rq y
  set S := Sq y
  set U := Uq w
  set X := Xq w
  set s := √2 with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  set L := 6 + 6 * s
  have hL : 0 < L := by positivity
  have hP0 : 0 ≤ P := Pq_nonneg y
  have hA : P * (L + 6) + 2 * s * L * (R - S) = 6 * (2 + s) * (P + 2 * (R - S)) := by
    linear_combination 12 * (R - S) * sqrt2_sq
  have hB : P * (L + 6) + 2 * s * L * (R + S) = 6 * (2 + s) * (P + 2 * (R + S)) := by
    linear_combination 12 * (R + S) * sqrt2_sq
  have key : 2 * L * Phi y w = 12 * (L - U) * P + (U + X) * (P * (L + 6) + 2 * s * L * (R - S)) +
      (U - X) * (P * (L + 6) + 2 * s * L * (R + S)) := by
    simp only [Phi]; ring
  rw [hA, hB] at key
  have t1 : 0 ≤ 12 * (L - U) * P := by
    apply mul_nonneg _ hP0; linarith
  have t2 : 0 ≤ (U + X) * (6 * (2 + s) * (P + 2 * (R - S))) := by
    apply mul_nonneg (by linarith); positivity
  have t3 : 0 ≤ (U - X) * (6 * (2 + s) * (P + 2 * (R + S))) := by
    apply mul_nonneg (by linarith); positivity
  have : 0 ≤ 2 * L * Phi y w := by rw [key]; linarith
  have h2L : 0 < 2 * L := by positivity
  exact nonneg_of_mul_nonneg_right (by linarith) h2L |> fun h => by
    by_contra hneg; push Not at hneg
    have := mul_neg_of_pos_of_neg h2L hneg
    linarith

/-- **Dirichlet property**: every point of `T` is a point of its orbit closest to `p`. -/
theorem dirichlet {w : UpperHalfPlane} (hw : w ∈ Tset) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) :
    dist w p0 ≤ dist (γ • w) p0 := by
  obtain ⟨y, hy, hn, g, hg, hz⟩ := cover_y hγ
  have hpos := nrd_pos_of hn
  obtain ⟨hV1, hV2⟩ := vertex_cond hy hn
  rw [hz, dist_le_iff, Fp_smul hg hpos]
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hpos
  have := Phi_nonneg hV1 hV2 hw
  have : 0 ≤ Phi y w / ((nrd y : ℝ) * w.im) := div_nonneg this (by have := w.im_pos; positivity)
  linarith


/-! ## Null sets: circles and lines orthogonal to `ℝ` -/

open MeasureTheory

theorem null_quadric_C (α β δ : ℝ) (h : α ≠ 0 ∨ β ≠ 0 ∨ δ ≠ 0) :
    volume {z : ℂ | α * Complex.normSq z + β * z.re + δ = 0} = 0 := by
  rcases eq_or_ne α 0 with hα | hα
  · rcases eq_or_ne β 0 with hβ | hβ
    · have hδ : δ ≠ 0 := by tauto
      have : {z : ℂ | α * Complex.normSq z + β * z.re + δ = 0} = ∅ := by
        ext z; simp [hα, hβ, hδ]
      rw [this, measure_empty]
    · have : {z : ℂ | α * Complex.normSq z + β * z.re + δ = 0} =
          Complex.measurableEquivRealProd ⁻¹' ({-δ / β} ×ˢ Set.univ) := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Complex.measurableEquivRealProd_apply,
          Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true, hα, zero_mul, zero_add]
        constructor
        · intro hz; field_simp; linarith
        · intro hz; rw [hz]; field_simp; ring
      rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  · set r : ℝ := -β / (2 * α)
    set D : ℝ := (β ^ 2 - 4 * α * δ) / (4 * α ^ 2)
    refine measure_mono_null (t := Metric.sphere (r : ℂ) (√D)) ?_
      (Measure.addHaar_sphere volume _ _)
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    have e : dist z (r : ℂ) ^ 2 = D := by
      rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
      rw [Complex.normSq_apply] at hz
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      simp only [r, D]
      field_simp
      linear_combination (16 * α) * hz
    rw [Metric.mem_sphere, ← e, Real.sqrt_sq dist_nonneg]

theorem null_quadric (α β δ : ℝ) (h : α ≠ 0 ∨ β ≠ 0 ∨ δ ≠ 0) :
    volume {w : UpperHalfPlane | α * Complex.normSq (w : ℂ) + β * w.re + δ = 0} = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  refine setLIntegral_measure_zero _ _ (measure_mono_null ?_ (null_quadric_C α β δ h))
  rintro _ ⟨w, hw, rfl⟩
  exact hw

/-! ## Almost disjointness of the translates of `T` -/

theorem smul_eq_self {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hJ : y.imJ = 0) (hK : y.imK = 0) (z : UpperHalfPlane) :
    g • z = z := by
  have hdet := det_pos_of hg hn
  have hy0 : (y.re : ℝ) ≠ 0 := by
    intro h0
    have : nrd y = 0 := by
      simp only [nrd, hI, hJ, hK]; have : y.re = 0 := by exact_mod_cast h0
      simp [this]
    rw [this] at hn; exact lt_irrefl _ hn
  apply UpperHalfPlane.ext
  rw [coe_smul_eq hdet]
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg, iota_apply]; simp [hJ, hK]
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hg, iota_apply]; simp [hJ, hK]
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (y.re : ℝ) := by rw [hg, iota_apply]; simp [hI]
  simp only [num, denom, e00, e01, e10, e11]
  have hq : y.re ≠ 0 := by exact_mod_cast hy0
  have : (y.re : ℂ) ≠ 0 := by exact_mod_cast hq
  push_cast
  simp only [zero_mul, zero_add, add_zero]
  field_simp

/-- On `T ∩ γ⁻¹ T` the two Dirichlet inequalities are equalities: `Φ_y = 0`. -/
theorem Phi_zero {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs) {g : GL (Fin 2) ℝ} {y : B}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y) (hn : 0 < nrd y)
    (hz : ∀ z : UpperHalfPlane, γ • z = g • z) {w : UpperHalfPlane} (hw1 : w ∈ Tset)
    (hw2 : γ • w ∈ Tset) : Phi y w = 0 := by
  have d1 := dirichlet hw1 hγ
  have d2 := dirichlet hw2 (gs_inv hγ)
  rw [inv_smul_smul] at d2
  have heq : dist (γ • w) p0 = dist w p0 := le_antisymm d2 d1
  rw [hz, dist_eq_iff, Fp_smul hg hn] at heq
  have hnr : (0 : ℝ) < nrd y := by exact_mod_cast hn
  have hd : 0 < (nrd y : ℝ) * w.im := by have := w.im_pos; positivity
  have : Phi y w / ((nrd y : ℝ) * w.im) = 0 := by linarith
  rcases div_eq_zero_iff.1 this with h | h
  · exact h
  · exact absurd h hd.ne'

/-- The cone argument for a rotation about `p`. -/
theorem cone_rigid {g : GL (Fin 2) ℝ} {y : B} (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = iota y)
    (hn : 0 < nrd y) (hI : y.imI = 0) (hK : y.imK = 0) {w : UpperHalfPlane} (hw : w ∈ Tset)
    (hgw : g • w ∈ Tset)
    (hrot : ∀ U X : ℝ, X ≤ U → -X ≤ U →
      ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * X + 6 * ((y.re : ℝ) * y.imJ) * U ≤
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * U - 2 * ((y.re : ℝ) * y.imJ) * X →
      -(((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * X + 6 * ((y.re : ℝ) * y.imJ) * U) ≤
        ((y.re : ℝ) ^ 2 - 3 * (y.imJ : ℝ) ^ 2) * U - 2 * ((y.re : ℝ) * y.imJ) * X →
      U ≤ X ∨ U ≤ -X) :
    Uq w = Xq w ∨ Uq w = -Xq w := by
  obtain ⟨hu, hx⟩ := cone_smul hg hn hI hK w
  have hm : 0 < Complex.normSq (denom g w) := Complex.normSq_pos.2 (denom_ne_zero g w)
  obtain ⟨h1, h2, -⟩ := hw
  obtain ⟨k1, k2, -⟩ := hgw
  have k1' := mul_le_mul_of_nonneg_left k1 hm.le
  have k2' := mul_le_mul_of_nonneg_left k2 hm.le
  rw [hu, hx] at k1'
  rw [mul_neg, hu, hx] at k2'
  rcases hrot _ _ h1 h2 k1' k2' with h | h
  · left; linarith
  · right; linarith

theorem disjoint_T {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Γs)
    (hne : (fun z : UpperHalfPlane => γ • z) ≠ id) :
    volume (Tset ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' Tset) = 0 := by
  obtain ⟨y, hy, hn, g, hg, hz⟩ := cover_y hγ
  have hpos := nrd_pos_of hn
  by_cases hP : Pq y = 0
  · -- `y = a₀ + a₂ j` fixes `p`: the cone argument
    have hI : y.imI = 0 := by
      have : (y.imI : ℝ) = 0 := by simp only [Pq] at hP; nlinarith [sq_nonneg (y.imI : ℝ), sq_nonneg (y.imK : ℝ)]
      exact_mod_cast this
    have hK : y.imK = 0 := by
      have : (y.imK : ℝ) = 0 := by simp only [Pq] at hP; nlinarith [sq_nonneg (y.imI : ℝ), sq_nonneg (y.imK : ℝ)]
      exact_mod_cast this
    have hsub : Tset ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' Tset ⊆
        {w | 1 * Complex.normSq (w : ℂ) + (-6) * w.re + (-3) = 0} ∪
        {w | 1 * Complex.normSq (w : ℂ) + 6 * w.re + (-3) = 0} := by
      rintro w ⟨hw1, hw2⟩
      simp only [Set.mem_preimage, hz] at hw2
      obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff y).1 hy
      simp only at hI hK
      have hn3 : n3 = 0 := by exact_mod_cast (show (n3 : ℚ) = 0 by linarith)
      subst hn3
      have hn1 : n1 = 0 := by exact_mod_cast (show (n1 : ℚ) = 0 by simpa using hI)
      subst hn1
      have hN : ((2 * n0 + n2 : ℤ) : ℚ) ^ 2 + 3 * ((n2 : ℤ) : ℚ) ^ 2 = 4 * nrd ⟨(n0 : ℚ) + n2 / 2,
          (0 : ℤ) + (0 : ℤ) / 2, n2 / 2, (0 : ℤ) / 2⟩ := by
        simp only [nrd]; push_cast; ring
      have hb : (2 * n0 + n2) ^ 2 + 3 * n2 ^ 2 ≤ 24 := by
        have : nrd ⟨(n0 : ℚ) + n2 / 2, (0 : ℤ) + (0 : ℤ) / 2, n2 / 2, (0 : ℤ) / 2⟩ ≤ 6 := nrd_le_six hn
        have : ((2 * n0 + n2 : ℤ) : ℚ) ^ 2 + 3 * ((n2 : ℤ) : ℚ) ^ 2 ≤ 24 := by linarith
        exact_mod_cast this
      have hn2 : -2 ≤ n2 ∧ n2 ≤ 2 := by constructor <;> nlinarith
      have hn0 : -3 ≤ n0 ∧ n0 ≤ 3 := by constructor <;> nlinarith
      obtain ⟨a1, a2⟩ := hn2
      obtain ⟨b1, b2⟩ := hn0
      have key := fun hrot => cone_rigid hg hpos hI hK hw1 hw2 hrot
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      have hU : Uq w = Complex.normSq (w : ℂ) - 3 := rfl
      have hX : Xq w = 6 * w.re := rfl
      by_cases h20 : n2 = 0
      · subst h20
        exfalso; apply hne; funext z; rw [hz]
        exact smul_eq_self hg hpos (by simp) (by simp) (by simp) z
      · interval_cases n2 <;> (try omega) <;> interval_cases n0 <;> (try norm_num [nrd] at hn) <;>
          (rcases key (by
              intro U X h1 h2 h3 h4; by_contra h; push Not at h; obtain ⟨h5, h6⟩ := h
              (try norm_num at h3 h4) <;> linarith) with h | h <;>
            [left; right] <;> rw [hU, hX] at h <;> linarith)
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · exact null_quadric 1 (-6) (-3) (Or.inl one_ne_zero)
    · exact null_quadric 1 6 (-3) (Or.inl one_ne_zero)
  · -- `Φ_y = 0` is a circle or a line
    have hsub : Tset ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' Tset ⊆
        {w | (Pq y + 2 * √2 * Rq y) * Complex.normSq (w : ℂ) + (-12 * √2 * Sq y) * w.re +
          (3 * Pq y - 6 * √2 * Rq y) = 0} := by
      rintro w ⟨hw1, hw2⟩
      have := Phi_zero hγ hg hpos hz hw1 hw2
      simp only [Set.mem_ofPred_eq]
      rw [← this]; simp only [Phi, Uq, Xq]; ring
    refine measure_mono_null hsub (null_quadric _ _ _ ?_)
    by_contra h
    push Not at h
    obtain ⟨h1, -, h3⟩ := h
    exact hP (by linarith)

end HDec.GammaStarArea



namespace HDec.GammaStarArea.AreaCalc

open Real

/-- `L = 1 + √2`, `k = 9 + 6√2`. -/
def LL : ℝ := 1 + √2
def kk : ℝ := 9 + 6 * √2

/-- `h(x) = 1/√(3 + 6|x| − x²) − 1/√(k − x²)`: the `y`-integral of `dy/y²` over the vertical section of `T`. -/
def hc (x : ℝ) : ℝ := 1 / √(3 + 6 * |x| - x ^ 2) - 1 / √(kk - x ^ 2)

theorem s2_sq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s3_sq : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
theorem s3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
theorem s2_lt : √2 < (3 / 2 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem s2_gt : (1 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem LL_pos : 0 < LL := by unfold LL; linarith [s2_pos]
theorem LL_lt : LL < 3 := by unfold LL; linarith [s2_lt]

theorem kk_sub_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < kk - x ^ 2 := by
  have h1 : x ^ 2 ≤ LL ^ 2 := by
    have := abs_nonneg x
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ LL ^ 2 := by gcongr
  unfold kk; unfold LL at h1; nlinarith [s2_sq, s2_pos]

theorem lo_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < 3 + 6 * |x| - x ^ 2 := by
  have h0 := abs_nonneg x
  have h1 := LL_lt
  have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith

theorem hc_neg (x : ℝ) : hc (-x) = hc x := by simp [hc, abs_neg]

theorem hc_cont : ContinuousOn hc (Set.Icc (-LL) LL) := by
  intro x hx
  have hx' : |x| ≤ LL := abs_le.2 hx
  apply ContinuousAt.continuousWithinAt
  unfold hc
  apply ContinuousAt.sub
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (lo_pos hx')).ne'
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (kk_sub_pos hx')).ne'

/-- `√k = √3 (1 + √2)`. -/
theorem sqrt_kk : √kk = √3 * LL := by
  have : kk = (√3 * LL) ^ 2 := by
    unfold kk LL; rw [mul_pow, s3_sq]; nlinarith [s2_sq]
  rw [this, Real.sqrt_sq (by have := s3_pos; have := LL_pos; positivity)]

theorem arcsin_sqrt3_half : arcsin (√3 / 2) = π / 3 := by
  rw [← Real.sin_pi_div_three, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-- `arcsin((√2 − 2)/(2√3)) = arcsin(1/√3) − π/4`. -/
theorem arcsin_key : arcsin ((√2 - 2) / (2 * √3)) = arcsin (1 / √3) - π / 4 := by
  set a := arcsin (1 / √3)
  have h3 := s3_pos
  have hb : 1 / √3 ≤ 1 := by
    rw [div_le_one h3]; rw [Real.le_sqrt' one_pos]; norm_num
  have hb' : -1 ≤ 1 / √3 := by linarith [show (0 : ℝ) ≤ 1 / √3 by positivity]
  have hsa : sin a = 1 / √3 := Real.sin_arcsin hb' hb
  have hca : cos a = √(1 - (1 / √3) ^ 2) := Real.cos_arcsin _
  have hc2 : √(1 - (1 / √3) ^ 2) = √2 / √3 := by
    rw [show 1 - (1 / √3) ^ 2 = 2 / 3 by rw [div_pow, s3_sq]; norm_num, Real.sqrt_div' 2 (by norm_num : (0:ℝ) ≤ 3)]
  have hsin : sin (a - π / 4) = (√2 - 2) / (2 * √3) := by
    rw [Real.sin_sub, hsa, hca, hc2, Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp
    nlinarith [s2_sq]
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.2 (by positivity)
  have ha1 : a ≤ π / 2 := Real.arcsin_le_pi_div_two _
  rw [← hsin, Real.arcsin_sin] <;> linarith [Real.pi_pos]

theorem hasDerivAt_F {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ LL) :
    HasDerivAt (fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk)) (hc x) x := by
  have h3 := s3_pos
  have hk := kk_sub_pos (x := x) (by rw [abs_of_nonneg hx0]; exact hxL)
  have hk0 : 0 < kk := by unfold kk; linarith [s2_pos]
  have hsk : 0 < √kk := Real.sqrt_pos.2 hk0
  have hL3 := LL_lt
  -- the arguments stay in `(-1, 1)`
  have hu1 : -1 < (x - 3) / (2 * √3) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [s3_sq, Real.sqrt_nonneg 3, show (3 / 2 : ℝ) < √3 by rw [Real.lt_sqrt (by norm_num)]; norm_num]
  have hu2 : (x - 3) / (2 * √3) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hv1 : -1 < x / √kk := by
    have : 0 ≤ x / √kk := by positivity
    linarith
  have hv2 : x / √kk < 1 := by
    rw [div_lt_one hsk, Real.lt_sqrt hx0]; linarith
  have hu : HasDerivAt (fun x : ℝ => (x - 3) / (2 * √3)) (1 / (2 * √3)) x :=
    ((hasDerivAt_id x).sub_const 3).div_const _
  have hv : HasDerivAt (fun x : ℝ => x / √kk) (1 / √kk) x := (hasDerivAt_id x).div_const _
  have hA := (Real.hasDerivAt_arcsin hu1.ne' hu2.ne).comp x hu
  have hB := (Real.hasDerivAt_arcsin hv1.ne' hv2.ne).comp x hv
  refine (hA.sub hB).congr_deriv ?_
  unfold hc
  rw [abs_of_nonneg hx0]
  congr 1
  · have hw : 0 ≤ 1 - ((x - 3) / (2 * √3)) ^ 2 := by nlinarith
    have e : √(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3) = √(3 + 6 * x - x ^ 2) := by
      have hsq : (√(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3)) ^ 2 = 3 + 6 * x - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, mul_pow, div_pow, mul_pow, s3_sq]; field_simp; ring
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp
  · have hw : 0 ≤ 1 - (x / √kk) ^ 2 := by nlinarith
    have e : √(1 - (x / √kk) ^ 2) * √kk = √(kk - x ^ 2) := by
      have hsq : (√(1 - (x / √kk) ^ 2) * √kk) ^ 2 = kk - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, div_pow, Real.sq_sqrt hk0.le]; field_simp
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp

theorem integral_half : ∫ x in (0 : ℝ)..LL, hc x = π / 12 := by
  have hL := LL_pos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk))]
  · simp only [zero_sub, zero_div, Real.arcsin_zero, sub_zero]
    have e1 : (-3) / (2 * √3) = -(√3 / 2) := by
      have := s3_pos; field_simp; nlinarith [s3_sq]
    have e2 : LL / √kk = 1 / √3 := by
      rw [sqrt_kk]; have := s3_pos; field_simp
    have e3 : (LL - 3) / (2 * √3) = (√2 - 2) / (2 * √3) := by unfold LL; ring_nf
    rw [e1, e2, e3, Real.arcsin_neg, arcsin_sqrt3_half, arcsin_key]
    ring
  · intro x hx
    rw [Set.uIcc_of_le hL.le] at hx
    exact hasDerivAt_F hx.1 hx.2
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)

theorem integral_full : ∫ x in (-LL)..LL, hc x = π / 6 := by
  have hL := LL_pos
  have hi1 : IntervalIntegrable hc MeasureTheory.volume (-LL) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hc_cont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hi2 : IntervalIntegrable hc MeasureTheory.volume 0 LL := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, integral_half]
  have : ∫ x in (-LL)..0, hc x = ∫ x in (0 : ℝ)..LL, hc x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := LL) hc
    simp only [neg_zero, hc_neg] at h
    exact h.symm
  rw [this, integral_half]; ring


/-! ## The measure-theoretic part -/

open MeasureTheory

/-- The triangle `T` in `ℂ`. -/
def TC : Set ℂ := {z : ℂ | 0 < z.im ∧ 6 * z.re ≤ Complex.normSq z - 3 ∧
  -(6 * z.re) ≤ Complex.normSq z - 3 ∧ Complex.normSq z - 3 ≤ 6 + 6 * √2}

/-- `T` in coordinates. -/
def Rr : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ 6 * q.1 ≤ q.1 ^ 2 + q.2 ^ 2 - 3 ∧
  -(6 * q.1) ≤ q.1 ^ 2 + q.2 ^ 2 - 3 ∧ q.1 ^ 2 + q.2 ^ 2 - 3 ≤ 6 + 6 * √2}

theorem measurableSet_Rr : MeasurableSet Rr := by
  unfold Rr
  have m1 : Measurable fun q : ℝ × ℝ => 6 * q.1 := by fun_prop
  have m2 : Measurable fun q : ℝ × ℝ => -(6 * q.1) := by fun_prop
  have m3 : Measurable fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 - 3 := by fun_prop
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le m1 m3).inter ((measurableSet_le m2 m3).inter (measurableSet_le m3 measurable_const)))

theorem TC_eq : TC = Complex.measurableEquivRealProd ⁻¹' Rr := by
  ext z
  simp only [TC, Rr, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_ofPred_eq,
    Complex.normSq_apply]
  ring_nf

/-- The integrand `dy/y²`. -/
def G (q : ℝ × ℝ) : ENNReal := ENNReal.ofReal (1 / q.2 ^ 2)

theorem measurable_G : Measurable G := by unfold G; fun_prop

theorem mem_Rr_iff {x y : ℝ} (hx : |x| ≤ LL) :
    (x, y) ∈ Rr ↔ y ∈ Set.Icc (√(3 + 6 * |x| - x ^ 2)) (√(kk - x ^ 2)) := by
  have hlo := lo_pos hx
  have hk := kk_sub_pos hx
  simp only [Rr, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hy, h1, h2, h3⟩
    refine ⟨(Real.sqrt_le_left hy.le).2 ?_, (Real.le_sqrt' hy).2 ?_⟩
    · rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    · unfold kk; linarith
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.sqrt_pos.2 hlo) h1
    have e1 := (Real.sqrt_le_left hy.le).1 h1
    have e2 := (Real.le_sqrt' hy).1 h2
    refine ⟨hy, ?_, ?_, ?_⟩
    · have := le_abs_self x; linarith
    · have := neg_abs_le x; linarith
    · unfold kk at e2; linarith

theorem not_mem_Rr {x y : ℝ} (hx : LL < |x|) : (x, y) ∉ Rr := by
  rintro ⟨hy, h1, h2, h3⟩
  have : 6 * |x| ≤ 6 + 6 * √2 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  unfold LL at hx; linarith

/-- `∫ dy/y²` over `[a, b]`. -/
theorem lintegral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ y in Set.Icc a b, ENNReal.ofReal (1 / y ^ 2) = ENNReal.ofReal (1 / a - 1 / b) := by
  have hcont : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (Set.Icc a b) := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    have : 0 < y := lt_of_lt_of_le ha hy.1
    positivity
  have hint : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Icc a b) := hcont.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc (fun y hy => by positivity))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => -(1 / y))]
  · ring
  · intro y hy
    rw [Set.uIcc_of_le hab] at hy
    have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have := (hasDerivAt_inv hy0).neg
    convert this using 1
    · funext t; simp
    · field_simp
  · exact (hcont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

theorem inner_eq (x : ℝ) :
    ∫⁻ y, Rr.indicator G (x, y) = ENNReal.ofReal ((Set.Icc (-LL) LL).indicator hc x) := by
  by_cases hx : |x| ≤ LL
  · have hx' : x ∈ Set.Icc (-LL) LL := abs_le.1 hx
    rw [Set.indicator_of_mem hx']
    have hlo := lo_pos hx
    have hk := kk_sub_pos hx
    have hle : √(3 + 6 * |x| - x ^ 2) ≤ √(kk - x ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : 6 * |x| ≤ 6 + 6 * √2 := by unfold LL at hx; linarith
      unfold kk; linarith
    have e : (fun y => Rr.indicator G (x, y)) =
        (Set.Icc (√(3 + 6 * |x| - x ^ 2)) (√(kk - x ^ 2))).indicator
          (fun y => ENNReal.ofReal (1 / y ^ 2)) := by
      funext y
      by_cases hy : (x, y) ∈ Rr
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((mem_Rr_iff hx).1 hy)]; rfl
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy ((mem_Rr_iff hx).2 h))]
    rw [e, lintegral_indicator measurableSet_Icc, lintegral_inv_sq (Real.sqrt_pos.2 hlo) hle]
    rfl
  · push Not at hx
    have hx' : x ∉ Set.Icc (-LL) LL := fun h => by
      have := abs_le.2 h; linarith
    rw [Set.indicator_of_notMem hx', ENNReal.ofReal_zero]
    have : (fun y => Rr.indicator G (x, y)) = fun _ => 0 := by
      funext y; exact Set.indicator_of_notMem (not_mem_Rr hx) _
    rw [this, lintegral_zero]

theorem hc_nonneg {x : ℝ} (hx : x ∈ Set.Icc (-LL) LL) : 0 ≤ hc x := by
  have hx' : |x| ≤ LL := abs_le.2 hx
  have hlo := lo_pos hx'
  have hk := kk_sub_pos hx'
  unfold hc
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 hlo)
  apply Real.sqrt_le_sqrt
  have : 6 * |x| ≤ 6 + 6 * √2 := by unfold LL at hx'; linarith
  unfold kk; linarith

/-- **The hyperbolic area of `T` is `π/6`.** -/
theorem area_TC : ∫⁻ z in TC, ENNReal.ofReal (1 / z.im ^ 2) = ENNReal.ofReal (π / 6) := by
  have h1 : ∫⁻ z in TC, ENNReal.ofReal (1 / z.im ^ 2) =
      ∫⁻ z in Complex.measurableEquivRealProd ⁻¹' Rr, G (Complex.measurableEquivRealProd z) := by
    rw [TC_eq]; rfl
  rw [h1, Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding G Rr]
  rw [← lintegral_indicator measurableSet_Rr, Measure.volume_eq_prod,
    lintegral_prod _ ((measurable_G.indicator measurableSet_Rr).aemeasurable)]
  simp_rw [inner_eq]
  have hint : Integrable ((Set.Icc (-LL) LL).indicator hc) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hc_cont.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [LL_pos]), integral_full]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ Set.Icc (-LL) LL
    · rw [Set.indicator_of_mem hx]; exact hc_nonneg hx
    · rw [Set.indicator_of_notMem hx]; simp

end HDec.GammaStarArea.AreaCalc

namespace HDec.GammaStarArea

open LeafQCheck LeafQCheck.QMglue PkgI1 MeasureTheory

local notation "p0" => HSyn.G0Split.FibreQM.PeriodMap.tau3

/-! ## Assembly -/

theorem measurableSet_T : MeasurableSet Tset := by
  have hU : Measurable Uq := by
    unfold Uq; exact ((Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable).sub_const _
  have hX : Measurable Xq := by
    unfold Xq; exact (UpperHalfPlane.continuous_re.measurable).const_mul _
  exact (measurableSet_le hX hU).inter ((measurableSet_le hX.neg hU).inter
    (measurableSet_le hU measurable_const))

theorem T_im {w : UpperHalfPlane} (hw : w ∈ Tset) : 1 ≤ w.im := by
  obtain ⟨h1, h2, h3⟩ := hw
  simp only [Uq, Xq] at h1 h2 h3
  have hn : Complex.normSq (w : ℂ) = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [hn] at h1 h2 h3
  have hs := AreaCalc.s2_lt
  have him := w.im_pos
  nlinarith [abs_nonneg w.re, sq_abs w.re]

theorem isCompact_T : IsCompact Tset := by
  have hcl : IsClosed Tset := by
    have hU : Continuous Uq := by
      unfold Uq; exact (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).sub continuous_const
    have hX : Continuous Xq := by unfold Xq; exact continuous_const.mul UpperHalfPlane.continuous_re
    exact (isClosed_le hX hU).inter ((isClosed_le hX.neg hU).inter (isClosed_le hU continuous_const))
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  rw [Metric.isBounded_iff_subset_closedBall p0]
  refine ⟨43, fun w hw => ?_⟩
  rw [Metric.mem_closedBall]
  have him := T_im hw
  obtain ⟨-, -, h3⟩ := hw
  have hs := AreaCalc.s2_lt
  have h3' : Complex.normSq (w : ℂ) ≤ 18 := by simp only [Uq] at h3; linarith
  have hF : Fp w ≤ 21 := by
    unfold Fp
    rw [div_le_iff₀ (by linarith)]
    have : Complex.normSq ((w : ℂ) - (p0 : ℂ)) ≤ Complex.normSq (w : ℂ) + 3 := by
      rw [p0_coe, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      have h3s : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      have := w.im_pos
      nlinarith [Real.sqrt_nonneg 3]
    nlinarith
  have hc : Real.cosh (dist w p0) ≤ 22 := by
    rw [cosh_dist_p0]
    have h3 : (1 : ℝ) ≤ 2 * √3 := by
      have : (1 : ℝ) ≤ √3 := by rw [Real.le_sqrt' one_pos]; norm_num
      linarith
    have hF0 : 0 ≤ Fp w := div_nonneg (Complex.normSq_nonneg _) w.im_pos.le
    have : Fp w / (2 * √3) ≤ Fp w := div_le_self hF0 h3
    linarith
  have hd : dist w p0 + 1 ≤ 2 * Real.cosh (dist w p0) := by
    rw [Real.cosh_eq]
    have := Real.add_one_le_exp (dist w p0)
    have := Real.exp_pos (-dist w p0)
    linarith
  linarith

theorem image_T : ((↑) : UpperHalfPlane → ℂ) '' Tset = AreaCalc.TC := by
  ext z
  constructor
  · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨w.im_pos, h1, h2, h3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨z, h0⟩, ⟨h1, h2, h3⟩, rfl⟩

theorem volume_T : volume Tset = ENNReal.ofReal (Real.pi / 6) := by
  rw [UpperHalfPlane.volume_eq_lintegral, image_T, ← AreaCalc.area_TC]
  refine setLIntegral_congr_fun (by
    rw [← image_T]; exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.2 measurableSet_T)
    (fun z hz => ?_)
  have h0 : 0 < z.im := hz.1
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos h0]
  ring

/-- **`Γ*` is a cocompact Fuchsian group with a fundamental domain of hyperbolic area `π/6`**
(`HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea`, TailZ2), with no hypotheses. -/
theorem gammaStarCocompactArea_proof : HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea :=
  ⟨⟨gs_one, fun a ha b hb => gs_mul ha hb, fun a ha => gs_inv ha, fun a ha => det_pos_of_mem ha,
      properlyDiscontinuous, ⟨Tset, isCompact_T, cover_T⟩⟩,
    Tset, ⟨measurableSet_T, cover_T, fun γ hγ hne => disjoint_T hγ hne⟩, volume_T⟩

end HDec.GammaStarArea



namespace HDec.GammaStarArea

open LeafQCheck LeafQCheck.QMglue PkgI1 MeasureTheory
open scoped Pointwise

/-! ## Shimizu's covolume of `𝒪¹` (the open leaf `shimizuCovolumeO1`), from `T` and the four cosets -/

/-- `s₁ = ⋃ᵢ rᵢ⁻¹ T` (`rᵢ = 1, x₄, x₆, x₄x₆`): a fundamental domain of `Γ¹`. -/
def S1 : Set UpperHalfPlane := ⋃ i : Fin 4, (g4 i)⁻¹ • Tset

theorem gamma1_iff' {h : GL (Fin 2) ℝ} : h ∈ HM.QMSplit.Gamma1 ↔ h ∈ QMSplitVB.Gamma1 := Iff.rfl

theorem mem_S1 {z : UpperHalfPlane} : z ∈ S1 ↔ ∃ i : Fin 4, g4 i • z ∈ Tset := by
  simp only [S1, Set.mem_iUnion, Set.mem_inv_smul_set_iff]

theorem cover_S1 (z : UpperHalfPlane) : ∃ h ∈ QMSplitVB.Gamma1, h • z ∈ S1 := by
  obtain ⟨γ, hγ, hT⟩ := cover_T z
  obtain ⟨i, h, hh, hz⟩ := cover_mob hγ
  exact ⟨h, hh, mem_S1.2 ⟨i, by rw [← hz]; exact hT⟩⟩

theorem isCompact_S1 : IsCompact S1 :=
  isCompact_iUnion fun i => isCompact_T.smul _

theorem measurableSet_S1 : MeasurableSet S1 :=
  MeasurableSet.iUnion fun i => measurableSet_T.const_smul _

/-- `T ∩ γ⁻¹ T` for `γ = r_j h r_i⁻¹`: null unless `i = j` and `h` acts trivially. -/
theorem piece_null {i j : Fin 4} {h : GL (Fin 2) ℝ} (hh : h ∈ QMSplitVB.Gamma1)
    (hne : ¬ (i = j ∧ ∀ z : UpperHalfPlane, h • z = z)) :
    volume ((g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset)) = 0 := by
  set γ := g4 j * h * (g4 i)⁻¹ with hγdef
  have hγ : γ ∈ Γs := gs_mul (gs_mul (g4_mem j) (gamma1_sub hh)) (gs_inv (g4_mem i))
  have hγne : (fun z : UpperHalfPlane => γ • z) ≠ id := by
    intro hid
    apply hne
    have key : ∀ u : UpperHalfPlane, g4 i • u = g4 j • (h • u) := by
      intro u
      have := congrFun hid (g4 i • u)
      simp only [id, hγdef, mul_smul, inv_smul_smul] at this
      exact this.symm
    have hij : j = i := coset_eq hh key
    subst hij
    refine ⟨rfl, fun z => ?_⟩
    have := key z
    exact (smul_left_cancel _ this).symm
  have e : (g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset) =
      (fun z : UpperHalfPlane => g4 i • z) ⁻¹' (Tset ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' Tset) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_inv_smul_set_iff, hγdef, mul_smul,
      inv_smul_smul]
  rw [e, measure_preimage_smul]
  exact disjoint_T hγ hγne

theorem null_S1 {h : GL (Fin 2) ℝ} (hh : h ∈ QMSplitVB.Gamma1)
    (hne : (fun z : UpperHalfPlane => h • z) ≠ id) :
    volume (S1 ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' S1) = 0 := by
  have e : S1 ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' S1 =
      ⋃ i : Fin 4, ⋃ j : Fin 4, ((g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset)) := by
    ext z
    simp only [S1, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; exact ⟨i, j, hi, hj⟩
    · rintro ⟨i, j, hi, hj⟩; exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [e]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => piece_null hh ?_
  rintro ⟨-, htriv⟩
  exact hne (funext htriv)

theorem volume_S1 : volume S1 = ENNReal.ofReal (2 * Real.pi / 3) := by
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i : Fin 4 => (g4 i)⁻¹ • Tset) := by
    intro i j hij
    have := piece_null (i := i) (j := j) (h := 1) one_mem_gamma1 (fun h => hij h.1)
    simpa [AEDisjoint] using this
  rw [S1, measure_iUnion₀ hdisj (fun i => (measurableSet_T.const_smul _).nullMeasurableSet),
    tsum_fintype, Fin.sum_univ_four]
  simp only [measure_smul, volume_T]
  have hp : 0 ≤ Real.pi / 6 := by positivity
  rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp,
    ← ENNReal.ofReal_add (by positivity) hp]
  congr 1; ring

/-- **Shimizu's covolume of `𝒪¹`** (`HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1`, the open leaf
`shimizuCovolumeO1`), with no hypotheses: `Γ¹` is cocompact Fuchsian with fundamental domain
`s₁ = ⋃ᵢ rᵢ⁻¹ T` of hyperbolic area `4 · π/6 = 2π/3`. -/
theorem shimizuCovolumeO1_proof : HM.QMSplit.ShimizuCovolumeO1 :=
  ⟨⟨one_mem_gamma1, fun a ha b hb => mul_mem_gamma1 ha hb, fun a ha => inv_mem_gamma1 ha,
      fun a ha => det_pos_of_mem (gamma1_sub ha),
      fun K hK => (properlyDiscontinuous K hK).subset (by
        rintro f ⟨γ, hγ, hf, hne⟩; exact ⟨γ, gamma1_sub hγ, hf, hne⟩),
      ⟨S1, isCompact_S1, cover_S1⟩⟩,
    S1, ⟨measurableSet_S1, cover_S1, fun γ hγ hne => null_S1 hγ hne⟩, volume_S1⟩

end HDec.GammaStarArea


/-! ## The rerouted consumers (alternative to filling `shimizuCovolumeO1`) -/

namespace HDec.GammaStarArea

open LeafQCheck

/-- `GammaStarFromO1` (qm-glue) holds trivially now. -/
theorem gammaStarFromO1_trivial : HM.QMSplit.GammaStarFromO1 := fun _ => gammaStarCocompactArea_proof

/-- Row H-87 from the valence formula alone (replaces `valenceFormulaGammaStar_of_leaves hV hS`). -/
theorem valenceFormulaGammaStar_noShimizu (hV : HM.QMSplit.ValenceFormulaCocompactEq) :
    VB.ValenceFormulaGammaStar :=
  HM.QMSplit.valenceFormulaGammaStar_of_eq (hV := hV) (hA := gammaStarCocompactArea_proof)

/-- Row H-88 without Shimizu (replaces `qmHauptmodulBase3_of_leaves hT hV hS hI`). -/
theorem qmHauptmodulBase3_noShimizu (hT : PkgI1.ThetaModularity) (hV : HM.QMSplit.ValenceFormulaCocompactEq)
    (hI : HM.QMSplit.Value24.IgusaCMValue24) : HM.QMHauptmodulBase3 :=
  HM.QMSplit.qmHauptmodulBase3_of' hT hV gammaStarCocompactArea_proof
    (HM.QMSplit.Value24.thetaQuotientValue24_of_igusa hI)

end HDec.GammaStarArea
