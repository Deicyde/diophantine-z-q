/-! ## assemble-port: `scratch/period-glue/W8.lean`, verbatim minus `import`/`#print` lines (mk/mk_pg.py) -/

/-! # period-glue: `S8WeightExact` from Igusa's `ThetaModularity` and the generation of `Γ*`

Task period-glue, 2026-11-13. `S8WeightExact` (period-map, `PGLight`, unchanged) is proved from
* `PkgI1.ThetaModularity` (**LEAF**, Igusa; pkg-I1's statement, unchanged), and
* `GammaStarGen` (**LEAF candidate**: `Γ* = ℚ^×·⟨ι(1+i+j), ι((j−3)/2)⟩`, a consequence of the
  published signature `(0; 2, 4, 6)` of `Γ*/ℚ^×` with Poincaré's polygon theorem; flagged for a
  human check),
by `s8WeightExact_of`. Proved here, with no other input:
* the elements of `GL₂(ℝ)⁺` for which `G8` has the exact automorphy form a subgroup
  (`G8AutoSubgroup`; the cocycle of `denom`), containing the rational scalars;
* the modular embedding of the two generators: explicit `M ∈ Sp₄(ℤ)` with
  `Ω(gτ) = M·Ω(τ)` and `det g · det(CΩ(τ) + D)(τ−3)(τ+1) = −(cτ+d)²(gτ−3)(gτ+1)`
  (`py/modemb.py` found them; the `linear_combination` coefficients are from `py/w8_lean.py`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Matrix HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap
open UpperHalfPlane (num denom σ coe_smul_of_det_pos denom_ne_zero)

/-! ### The automorphy subgroup -/

/-- `g ∈ GL₂(ℝ)⁺` and `G8` has the exact automorphy of `S8WeightExact` for `g`. -/
def G8Auto (γ : GL (Fin 2) ℝ) : Prop :=
  0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ∧ ∀ z : UpperHalfPlane,
    G8 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ z ^ 8 * G8 (z : ℂ)

theorem detv (g : GL (Fin 2) ℝ) : (g.det : ℝ) = (g : Matrix (Fin 2) (Fin 2) ℝ).det :=
  Matrix.GeneralLinearGroup.val_det_apply g

theorem σ_of_pos {g : GL (Fin 2) ℝ} (h : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (w : ℂ) :
    σ g w = w := by
  have h' : 0 < (g.det : ℝ) := by rwa [detv]
  simp only [σ, if_pos h', ContinuousAlgEquiv.refl_apply]

theorem denom_mul_pos (g h : GL (Fin 2) ℝ) (hh : 0 < (h : Matrix (Fin 2) (Fin 2) ℝ).det)
    (z : UpperHalfPlane) : denom (g * h) z = denom g ((h • z : UpperHalfPlane) : ℂ) * denom h z := by
  rw [UpperHalfPlane.denom_cocycle_σ, σ_of_pos hh]

theorem g8Auto_one : G8Auto 1 := by
  refine ⟨by simp, fun z => ?_⟩
  simp [UpperHalfPlane.denom]

theorem g8Auto_mul {g h : GL (Fin 2) ℝ} (hg : G8Auto g) (hh : G8Auto h) : G8Auto (g * h) := by
  refine ⟨by rw [Units.val_mul, det_mul]; exact mul_pos hg.1 hh.1, fun z => ?_⟩
  rw [mul_smul, denom_mul_pos g h hh.1, Units.val_mul, det_mul]
  have e1 := hg.2 (h • z)
  have e2 := hh.2 z
  push_cast
  calc G8 ((g • h • z : UpperHalfPlane) : ℂ) *
        (((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) * ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ)) ^ 4
      = (G8 ((g • h • z : UpperHalfPlane) : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4 := by ring
    _ = denom g ((h • z : UpperHalfPlane) : ℂ) ^ 8 * (G8 ((h • z : UpperHalfPlane) : ℂ) *
          ((h : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4) := by rw [e1]; ring
    _ = _ := by rw [e2]; ring

theorem g8Auto_inv {g : GL (Fin 2) ℝ} (hg : G8Auto g) : G8Auto g⁻¹ := by
  have hd : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
      ((g : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
    rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  refine ⟨by rw [hd]; exact inv_pos.mpr hg.1, fun z => ?_⟩
  set z' := g⁻¹ • z with hz'
  have e := hg.2 z'
  rw [hz', smul_inv_smul] at e
  have hc := denom_mul_pos g g⁻¹ (by rw [hd]; exact inv_pos.mpr hg.1) z
  rw [mul_inv_cancel] at hc
  have h1 : denom (1 : GL (Fin 2) ℝ) z = 1 := by simp [UpperHalfPlane.denom]
  rw [h1] at hc
  have hD : denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 := denom_ne_zero _ _
  have hdet : ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ≠ 0 := by exact_mod_cast hg.1.ne'
  rw [hd]
  push_cast
  have key : G8 ((g⁻¹ • z : UpperHalfPlane) : ℂ) = G8 (z : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) ^ 4 /
      denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ) ^ 8 := by
    rw [eq_div_iff (pow_ne_zero _ hD), e]; ring
  rw [key]
  have hinv : denom g⁻¹ z = (denom g ((g⁻¹ • z : UpperHalfPlane) : ℂ))⁻¹ :=
    (eq_inv_of_mul_eq_one_right hc.symm)
  rw [hinv]
  field_simp

theorem g8Auto_scalar {g : GL (Fin 2) ℝ} (q : ℚ) (hq : q ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1) : G8Auto g := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = (q : ℝ) ^ 2 := by
    rw [hg, Matrix.det_smul, Matrix.det_one]; simp
  have hpos : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; positivity
  have e00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by rw [hg]; simp
  have e01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by rw [hg]; simp
  have e10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by rw [hg]; simp
  have e11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = q := by rw [hg]; simp
  refine ⟨hpos, fun z => ?_⟩
  have hden : denom g z = (q : ℂ) := by simp [UpperHalfPlane.denom, e10, e11]
  have hsm : g • z = z := by
    ext1
    rw [coe_smul_of_det_pos (by rwa [detv]), hden]
    simp only [UpperHalfPlane.num, e00, e01]
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    field_simp
    push_cast; ring
  rw [hsm, hden, hdet]
  push_cast; ring

/-- The automorphy group of `G8` (a subgroup of `GL₂(ℝ)⁺`). -/
def G8AutoSubgroup : Subgroup (GL (Fin 2) ℝ) where
  carrier := {γ | G8Auto γ}
  one_mem' := g8Auto_one
  mul_mem' := g8Auto_mul
  inv_mem' := g8Auto_inv

/-! ### From the modular embedding of one element to its automorphy -/

theorem dF_ne {z : ℂ} (hz : 0 < z.im) : dF z ≠ 0 := by
  unfold dF
  have h2 : (√2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) h3) h4) two_ne_zero

theorem zz_ne {z : ℂ} (hz : 0 < z.im) : (z - 3) * (z + 1) ≠ 0 := by
  have h3 : z - 3 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  have h4 : z + 1 ≠ 0 := fun h => by have := congrArg Complex.im h; simp at this; linarith
  exact mul_ne_zero h3 h4

theorem sub3_add1_ne {z : ℂ} (hz : 0 < z.im) : z - 3 ≠ 0 ∧ z + 1 ≠ 0 :=
  ⟨fun h => by have := congrArg Complex.im h; simp at this; linarith,
   fun h => by have := congrArg Complex.im h; simp at this; linarith⟩

theorem g8Auto_of_sp (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (hrel : ∀ z : ℂ, 0 < z.im →
      PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 4 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    G8Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := (hT M hM (PkgI1.Omega z) (omegaSiegel_proof z z.im_pos)).1
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold G8
  rw [hw, hmod]
  have hf4 : (PkgI1.spFactor M (PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 4 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 4 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  generalize num g z / denom g z = w at *
  field_simp
  linear_combination (PkgI1.thetaSum8 (PkgI1.Omega z)) * hf4

/-! ### The two generators -/

/-- `x₄ = 1 + i + j` (reduced norm 2; `ι(x₄)` is elliptic of order 4 in `PSL₂(ℝ)`, fixing
`√2 + i`). -/
def x4 : PkgI1.B := ⟨1, 1, 1, 0⟩
/-- `x₆ = (j − 3)/2 = j(1+j)/2` (reduced norm 3; `ι(x₆)` is elliptic of order 6, fixing `i√3`). -/
def x6 : PkgI1.B := ⟨-3 / 2, 0, 1 / 2, 0⟩

/-- `Nf` homogenized: `V²·Nf(W/V)`. -/
def Nfh (W V : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(√2 : ℂ) * (W ^ 2 / 2 + W * V - 3 / 2 * V ^ 2) - W ^ 2 / 2 - 3 / 2 * V ^ 2,
     (√2 : ℂ) * (-W ^ 2 / 2 - W * V + 3 / 2 * V ^ 2) + W ^ 2 + 3 * V ^ 2;
     (√2 : ℂ) * (-W ^ 2 / 2 - W * V + 3 / 2 * V ^ 2) + W ^ 2 + 3 * V ^ 2,
     (√2 : ℂ) * (W ^ 2 + 2 * W * V - 3 * V ^ 2) - W ^ 2 - 3 * V ^ 2]

/-- `dF` homogenized: `V²·dF(W/V)`. -/
def dFh (W V : ℂ) : ℂ := -(√2 : ℂ) * (W - 3 * V) * (W + V) / 2

theorem Nf_hom (W V : ℂ) (hV : V ≠ 0) : Nf (W / V) = (V ^ 2)⁻¹ • Nfh W V := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nf, Nfh] <;> field_simp <;> ring

theorem dF_hom (W V : ℂ) (hV : V ≠ 0) : dF (W / V) = dFh W V / V ^ 2 := by
  simp only [dF, dFh]; field_simp

theorem omega_smul {z : ℂ} (hz : dF z ≠ 0) : PkgI1.Omega z = (dF z)⁻¹ • Nf z := by
  ext i j
  rw [omega_eq, Matrix.smul_apply, smul_eq_mul, div_eq_inv_mul]

/-- **`spAct` from a polynomial identity (proved).** -/
theorem spAct_of_poly (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (z W V : ℂ) (hV : V ≠ 0) (hz : dF z ≠ 0) (hw : dF (W / V) ≠ 0)
    (hP : (C * Nf z + dF z • D).det ≠ 0)
    (hI : dFh W V • (A * Nf z + dF z • B) = Nfh W V * (C * Nf z + dF z • D)) :
    PkgI1.spAct M (PkgI1.Omega z) = PkgI1.Omega (W / V) := by
  unfold PkgI1.spAct
  simp only [hM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [omega_smul hz, omega_smul hw, Nf_hom W V hV, dF_hom W V hV]
  set c := (dF z)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hz
  set P := C * Nf z + dF z • D with hPdef
  set X := A * Nf z + dF z • B with hX
  have hZ : C * (c • Nf z) + D = c • P := by
    rw [hPdef, smul_add, smul_smul, hc, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  have hY : A * (c • Nf z) + B = c • X := by
    rw [hX, smul_add, smul_smul, hc, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  rw [hZ, hY]
  have hdetZ : (c • P).det ≠ 0 := by
    rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc0) hP
  letI := Matrix.invertibleOfIsUnitDet (c • P) (isUnit_iff_ne_zero.mpr hdetZ)
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  have hdFh : dFh W V ≠ 0 := by
    intro h0; apply hw; rw [dF_hom W V hV, h0, zero_div]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hI.symm]
  match_scalars
  all_goals field_simp
  all_goals ring

/-! #### `g₄ = ι(1 + i + j)` -/

def A4 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
def B4 : Matrix (Fin 2) (Fin 2) ℂ := !![1, -2; -2, 2]
def C4 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def D4 : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 2; 1, -1]
/-- The symplectic matrix of `g₄` (`py/modemb.py`). -/
def M4 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  Matrix.fromBlocks !![1, 0; 0, 1] !![1, -2; -2, 2] !![0, 1; 1, 0] !![-1, 2; 1, -1]

theorem M4_map : M4.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A4 B4 C4 D4 := by
  unfold M4 A4 B4 C4 D4
  rw [Matrix.fromBlocks_map]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem M4_symp : M4 ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  unfold M4 Matrix.J
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_transpose]

theorem I1_g4 (z : ℂ) :
    dFh ((√2 : ℂ) * z + z - 3) (-(√2 : ℂ) + z + 1) • (A4 * Nf z + dF z • B4) =
      Nfh ((√2 : ℂ) * z + z - 3) (-(√2 : ℂ) + z + 1) * (C4 * Nf z + dF z • D4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A4, B4, C4, D4, Nf, Nfh, dF, dFh, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination ((√2 : ℂ)^2*z^3 - 6*(√2 : ℂ)^2*z^2 - 3*(√2 : ℂ)^2*z - (√2 : ℂ)*z^4/2 +
      7*(√2 : ℂ)*z^3 + 21*(√2 : ℂ)*z + 9*(√2 : ℂ)/2 - 2*z^4 - 12*z^2 - 18) * sqrt2_sq
  · linear_combination (-(√2 : ℂ)^2*z^4/4 - 2*(√2 : ℂ)^2*z^3 + 21*(√2 : ℂ)^2*z^2/2 +
      6*(√2 : ℂ)^2*z - 9*(√2 : ℂ)^2/4 + (√2 : ℂ)*z^4/2 - 11*(√2 : ℂ)*z^3 - 33*(√2 : ℂ)*z -
      9*(√2 : ℂ)/2 + 3*z^4 + 18*z^2 + 27) * sqrt2_sq
  · linear_combination (-(√2 : ℂ)^2*z^4/4 - 2*(√2 : ℂ)^2*z^3 + 21*(√2 : ℂ)^2*z^2/2 +
      6*(√2 : ℂ)^2*z - 9*(√2 : ℂ)^2/4 + (√2 : ℂ)*z^4/2 - 11*(√2 : ℂ)*z^3 - 33*(√2 : ℂ)*z -
      9*(√2 : ℂ)/2 + 3*z^4 + 18*z^2 + 27) * sqrt2_sq
  · linear_combination (2*(√2 : ℂ)^2*z^3 - 12*(√2 : ℂ)^2*z^2 - 6*(√2 : ℂ)^2*z - (√2 : ℂ)*z^4 +
      14*(√2 : ℂ)*z^3 + 42*(√2 : ℂ)*z + 9*(√2 : ℂ) - 4*z^4 - 24*z^2 - 36) * sqrt2_sq

theorem I2_g4 (z : ℂ) :
    (C4 * Nf z + dF z • D4).det * 2 * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * ((((√2 : ℂ) * z + z - 3) - 3 * (-(√2 : ℂ) + z + 1)) *
        (((√2 : ℂ) * z + z - 3) + (-(√2 : ℂ) + z + 1))) := by
  rw [Matrix.det_fin_two]
  simp [C4, D4, Nf, dF, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination ((√2 : ℂ)^2*z^6/4 - (√2 : ℂ)^2*z^5/2 - 13*(√2 : ℂ)^2*z^4/4 +
    5*(√2 : ℂ)^2*z^3 + 39*(√2 : ℂ)^2*z^2/4 - 9*(√2 : ℂ)^2*z/2 - 27*(√2 : ℂ)^2/4 - z^6/2 + z^5 -
    3*z^4/2 + 6*z^3 + 9*z^2/2 + 9*z + 27/2) * sqrt2_sq

/-! #### `g₆ = ι((j − 3)/2)` -/

def A6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 0]
def B6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]
def C6 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
def D6 : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 2; -1, 1]
/-- The symplectic matrix of `g₆` (`py/modemb.py`). -/
def M6 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  Matrix.fromBlocks !![0, 0; 0, 0] !![0, -1; 1, 0] !![0, 1; -1, 0] !![-1, 2; -1, 1]

theorem M6_map : M6.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A6 B6 C6 D6 := by
  unfold M6 A6 B6 C6 D6
  rw [Matrix.fromBlocks_map]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

theorem M6_symp : M6 ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff]
  unfold M6 Matrix.J
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.fromBlocks_transpose]

theorem I1_g6 (z : ℂ) :
    dFh (-3 * z / 2 - 3 / 2) (z / 2 - 3 / 2) • (A6 * Nf z + dF z • B6) =
      Nfh (-3 * z / 2 - 3 / 2) (z / 2 - 3 / 2) * (C6 * Nf z + dF z • D6) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A6, B6, C6, D6, Nf, Nfh, dF, dFh, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · linear_combination (-3*z^4/4 - 9*z^2/2 - 27/4) * sqrt2_sq
  · linear_combination (3*z^4/4 + 9*z^2/2 + 27/4) * sqrt2_sq
  · ring

theorem I2_g6 (z : ℂ) :
    (C6 * Nf z + dF z • D6).det * 3 * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * (((-3 * z / 2 - 3 / 2) - 3 * (z / 2 - 3 / 2)) *
        ((-3 * z / 2 - 3 / 2) + (z / 2 - 3 / 2))) := by
  rw [Matrix.det_fin_two]
  simp [C6, D6, Nf, dF, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (3*z^6/4 - 3*z^5/2 + 9*z^4/4 - 9*z^3 - 27*z^2/4 - 27*z/2 - 81/4) * sqrt2_sq

/-! ### Assembly -/

/-- **The automorphy factor from a polynomial identity (proved).** -/
theorem spFactor_of_poly (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (z W V detg : ℂ) (hV : V ≠ 0) (hz : dF z ≠ 0)
    (hI2 : (C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1)) =
      -1 * dF z ^ 2 * ((W - 3 * V) * (W + V))) :
    PkgI1.spFactor M (PkgI1.Omega z) * detg * ((z - 3) * (z + 1)) =
      -1 * V ^ 2 * ((W / V - 3) * (W / V + 1)) := by
  unfold PkgI1.spFactor
  simp only [hM, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [omega_smul hz]
  have hZ : C * ((dF z)⁻¹ • Nf z) + D = (dF z)⁻¹ • (C * Nf z + dF z • D) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, Matrix.mul_smul]
  rw [hZ, Matrix.det_smul, Fintype.card_fin]
  calc (dF z)⁻¹ ^ 2 * (C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1))
      = (dF z)⁻¹ ^ 2 * ((C * Nf z + dF z • D).det * detg * ((z - 3) * (z + 1))) := by ring
    _ = _ := by rw [hI2]; field_simp

/-- `G8` has the exact automorphy for `g = ι(x)` once the modular embedding identities hold. -/
theorem g8Auto_gen (hT : PkgI1.ThetaModularity) (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (hMs : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    G8Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g8Auto_of_sp hT g hdet M hMs (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem iota_x4 : PkgI1.iota x4 = !![1 + √2, -3; 1, 1 - √2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x4]

theorem iota_x6 : PkgI1.iota x6 = !![-3 / 2, -3 / 2; 1 / 2, -3 / 2] := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp [x6] <;> norm_num

theorem g8Auto_g4 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4) : G8Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen hT g (by rw [hdet]; norm_num) M4 M4_symp A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g8Auto_g6 (hT : PkgI1.ThetaModularity) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6) : G8Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen hT g (by rw [hdet]; norm_num) M6 M6_symp A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **LEAF candidate (generation of `Γ*`; flagged for a human check).** Every `γ ∈ Γ*` lies in
the subgroup of `GL₂(ℝ)` generated by `ι(1 + i + j)`, `ι((j − 3)/2)` and the rational scalars.

Source and derivation: `Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` (image in `PSL₂(ℝ)`) is a Fuchsian group of
signature `(0; 2, 4, 6)`, i.e. the `(2, 4, 6)` triangle group, of covolume
`2π(−2 + 1/2 + 3/4 + 5/6) = π/6` (Takeuchi, *Commensurability classes of arithmetic triangle
groups*, J. Fac. Sci. Univ. Tokyo 24 (1977), the class of `(2, 4, 6)` with quaternion algebra of
discriminant 6; Elkies, *Shimura curve computations*, ANTS 1998, §3 (`X*(6)` and the `(2,4,6)`
group); locators UNVERIFIED). Derivation of the stated form (model argument, numerics VERIFIED in
`py/triangle.py`): `g₄ = ι(1+i+j)` and `g₆ = ι((j−3)/2)` are elliptic of orders 4 and 6 in
`PSL₂(ℝ)` (`trd² / nrd = 2, 3`), fixing `√2 + i` and `i√3`; `x₂ = 2x₆x₄⁻¹ = (3/2)i + 2j + (1/2)ij`
has `trd = 0`, so `g₆g₄⁻¹` has order 2; the hyperbolic distance `d` of the two fixed points has
`cosh d = 1 + ((√2)² + (√3 − 1)²)/(2·√3) = √3 = cot(π/4)cot(π/6)`, which is the side of the
hyperbolic triangle with angles `π/4, π/6, π/2`. By Poincaré's polygon theorem (Beardon, *The
geometry of discrete groups*, §9.8 and §10.6, UNVERIFIED) `⟨g₄, g₆⟩` is the `(2,4,6)` triangle group
of that triangle, covolume `π/6`, so it has index 1 in `Γ*/ℚ^×`; an element of `N_B(𝒪)⁺` that is
a real multiple of a word in `x₄, x₆` is a rational multiple (the center of `B` is `ℚ`). -/
def GammaStarGen : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, γ ∈ Subgroup.closure
    ({γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x4} ∪
      {γ : GL (Fin 2) ℝ | (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x6} ∪
      {γ : GL (Fin 2) ℝ | ∃ q : ℚ, q ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = (q : ℝ) • 1})

/-- **`S8WeightExact` from Igusa's `ThetaModularity` and `GammaStarGen` (proved).** -/
theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hG : GammaStarGen) : S8WeightExact := by
  intro γ hγ z
  have hmem : γ ∈ G8AutoSubgroup := by
    refine (Subgroup.closure_le (K := G8AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g8Auto_g4 hT hg
    · exact g8Auto_g6 hT hg
    · exact g8Auto_scalar q hq hg
  exact hmem.2 z

end HSyn.G0Split.FibreQM.PeriodGlue

end  -- assemble-port: closes the file's `noncomputable section`
