import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Cd
import ZInQKernel.Contrib.GZStatements.Level
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Cusps.Basic

noncomputable section

open UpperHalfPlane WeierstrassCurve ZInQ.GZDecomp CongruenceSubgroup
open ZInQ.Contrib.HeckeFE
open Matrix.GeneralLinearGroup (upperRightHom)
open scoped MatrixGroups ZMod

namespace ZInQ.GZWeil

/-! ## §1. The Eichler integral of the theta series of `ψ_d` -/

/-- `Φ_d(τ) = Σ_{n ≥ 1} heckeCoeff d n / n · e^{2πinτ}`: the Eichler integral `2πi ∫_{i∞}^τ f_d`
of the theta series `f_d = Σ heckeCoeff d n qⁿ` of the Hecke character `ψ_d` of `C_d`. -/
def eichlerCd (d : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, heckeCoeff d (n + 1) / ((n : ℂ) + 1) *
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)

theorem norm_unitOf_le (t : ZMod 4 × ZMod 4) : ‖unitOf t‖ ≤ 1 := by
  unfold unitOf
  split_ifs <;> simp

theorem norm_jacobiSym_le (a : ℤ) (b : ℕ) : ‖(jacobiSym a b : ℂ)‖ ≤ 1 := by
  rcases jacobiSym.trichotomy a b with h | h | h <;> simp [h]

theorem norm_heckeCoeff_le (d m : ℕ) : ‖heckeCoeff d m‖ ≤ (2 * m + 1) ^ 3 := by
  unfold heckeCoeff
  have hcard : ((normFiber m).card : ℝ) ≤ (2 * m + 1) ^ 2 := by
    have : (normFiber m).card ≤ (2 * m + 1) ^ 2 := by
      unfold normFiber
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Int.card_Icc]
      have : ((m : ℤ) + 1 - -(m : ℤ)).toNat = 2 * m + 1 := by omega
      rw [this, sq]
    exact_mod_cast this
  have hterm : ∀ p ∈ normFiber m,
      ‖(jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) * unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) *
        gz 0 0 p‖ ≤ 2 * m + 1 := by
    intro p hp
    have hp' := mem_normFiber.mp hp
    rw [norm_mul, norm_mul]
    have h1 := norm_jacobiSym_le (p.1 ^ 2 + p.2 ^ 2) d
    have h2 := norm_unitOf_le ((p.1 : ZMod 4), (p.2 : ZMod 4))
    have h3 : ‖gz 0 0 p‖ ≤ 2 * m + 1 := by
      have hg : gz 0 0 p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by simp [gz]
      rw [hg]
      have hn : ‖((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖ ≤ |(p.1 : ℝ)| + |(p.2 : ℝ)| := by
        refine (norm_add_le _ _).trans ?_
        simp [Complex.norm_intCast]
      have hb1 : |(p.1 : ℝ)| ≤ m := by
        have : |p.1| ≤ m := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_abs p.1]
        exact_mod_cast this
      have hb2 : |(p.2 : ℝ)| ≤ m := by
        have : |p.2| ≤ m := by
          rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_abs p.2]
        exact_mod_cast this
      linarith
    calc ‖(jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ)‖ * ‖unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4))‖ *
          ‖gz 0 0 p‖ ≤ 1 * 1 * (2 * m + 1) := by gcongr
      _ = 2 * m + 1 := by ring
  rw [norm_mul]
  calc ‖(1 / 4 : ℂ)‖ * ‖∑ p ∈ normFiber m, (jacobiSym (p.1 ^ 2 + p.2 ^ 2) d : ℂ) *
        unitOf ((p.1 : ZMod 4), (p.2 : ZMod 4)) * gz 0 0 p‖
      ≤ 1 * ((normFiber m).card * (2 * m + 1)) := by
        gcongr
        · norm_num
        · refine (norm_sum_le _ _).trans ?_
          have := Finset.sum_le_card_nsmul _ _ _ hterm
          rwa [nsmul_eq_mul] at this
    _ ≤ 1 * ((2 * m + 1) ^ 2 * (2 * m + 1)) := by gcongr
    _ = (2 * m + 1) ^ 3 := by ring

theorem summable_eichler_term (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable fun n : ℕ => heckeCoeff d (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z) := by
  set r : ℝ := Real.exp (-2 * Real.pi * z.im) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  have hS : Summable fun n : ℕ => ((2 * (n : ℝ) + 3) ^ 3) * r ^ n := by
    have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (r := r) (by
      rw [Real.norm_of_nonneg hr0]; exact hr1)
    have := (((h3.mul_left 8).add (h2.mul_left 36)).add (h1.mul_left 54)).add (h0.mul_left 27)
    refine this.congr fun n => ?_
    ring
  refine Summable.of_norm_bounded hS fun n => ?_
  rw [norm_mul, norm_div]
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ = r ^ (n + 1) := by
    rw [Complex.norm_exp, hr, ← Real.exp_nat_mul]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.natCast_re,
      Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    ring
  have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_natCast]; push_cast; ring
  rw [he, hn1]
  have hb := norm_heckeCoeff_le d (n + 1)
  push_cast at hb
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hrn : r ^ (n + 1) ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)
  calc ‖heckeCoeff d (n + 1)‖ * r ^ (n + 1) ≤ (2 * ((n : ℝ) + 1) + 1) ^ 3 * r ^ n := by
        gcongr
    _ ≤ (2 * (n : ℝ) + 3) ^ 3 * r ^ n * ((n : ℝ) + 1) := by
        have : (2 * ((n : ℝ) + 1) + 1) = 2 * (n : ℝ) + 3 := by ring
        rw [this]
        have : 0 ≤ (2 * (n : ℝ) + 3) ^ 3 * r ^ n := by positivity
        nlinarith

/-! ## §2. The twist formula `d Φ_d(z) = Σ_a 𝓕χ(a) Φ₁(z + a/d)` -/

open ZInQ.GZTheta (jacobiChar jacobiChar_natCast heckeCoeff_eq_jacobiSym_mul)

/-- Fourier inversion on `ZMod d`: `Σ_a 𝓕Φ(a) e(ak/d) = d Φ(k)`. -/
theorem sum_dft_mul_stdAddChar (d : ℕ) [NeZero d] (Φ : ZMod d → ℂ) (k : ZMod d) :
    ∑ a : ZMod d, 𝓕 Φ a * ZMod.stdAddChar (a * k) = (d : ℂ) * Φ k := by
  have h := ZMod.invDFT_apply (𝓕 Φ) k
  rw [LinearEquiv.symm_apply_apply] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast NeZero.ne d), one_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_eq_mul, mul_comm]

theorem exp_translate (d : ℕ) [NeZero d] (a : ZMod d) (m : ℕ) (z : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (z + (a.val : ℂ) / d)) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * z) * ZMod.stdAddChar (a * (m : ZMod d)) := by
  have hcast : (a * (m : ZMod d)) = (((a.val * m : ℕ) : ℤ) : ZMod d) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [hcast, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The twist formula for Eichler integrals**: `d Φ_d(z) = Σ_{a mod d} 𝓕χ_d(a) Φ₁(z + a/d)`,
with `χ_d = (·/d)` (Tau Ceti's `twist_apply`, one level up: `Φ_d` is the Eichler integral of
`f₁ ⊗ χ_d`). -/
theorem twist_formula (d : ℕ) [NeZero d] {z : ℂ} (hz : 0 < z.im) :
    (d : ℂ) * eichlerCd d z =
      ∑ a : ZMod d, 𝓕 (jacobiChar d) a * eichlerCd 1 (z + (a.val : ℂ) / d) := by
  have hz' : ∀ a : ZMod d, 0 < (z + (a.val : ℂ) / d).im := fun a => by
    have : ((a.val : ℂ) / d).im = 0 := by
      rw [show ((a.val : ℂ) / d) = (((a.val : ℝ) / d : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_im _
    rw [Complex.add_im, this, add_zero]; exact hz
  simp only [eichlerCd]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun a _ => (summable_eichler_term 1 (hz' a)).mul_left _]
  congr 1
  funext n
  have key := sum_dft_mul_stdAddChar d (jacobiChar d) ((n + 1 : ℕ) : ZMod d)
  rw [jacobiChar_natCast] at key
  have e1 : ∀ a : ZMod d, 𝓕 (jacobiChar d) a *
      (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * (z + (a.val : ℂ) / d))) =
      (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z))
        * (𝓕 (jacobiChar d) a * ZMod.stdAddChar (a * ((n + 1 : ℕ) : ZMod d))) := by
    intro a
    have := exp_translate d a (n + 1) z
    rw [show (((n + 1 : ℕ)) : ℂ) = (n : ℂ) + 1 by push_cast; ring] at this
    rw [this]; ring
  rw [Finset.sum_congr rfl fun a _ => e1 a, ← Finset.mul_sum, key,
    heckeCoeff_eq_jacobiSym_mul d (n + 1)]
  push_cast
  ring

/-! ## §3. The periods of `Φ_d` over `Γ₀(32 d²)` through the periods of `Φ₁` over `Γ₀(32)` -/

open ZInQ.GZTheta (jacobiChar_sq_unit dvd_level_left dvd_level_right)
open Matrix.SpecialLinearGroup (mapGL)

/-- `𝓕χ(a u) = 𝓕χ(a)` for a unit `u` with `χ(u⁻¹) = 1`. -/
theorem dft_mul_unit (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (u : (ZMod d)ˣ)
    (hu : χ (u⁻¹ : (ZMod d)ˣ) = 1) (a : ZMod d) : 𝓕 χ (a * u) = 𝓕 χ a := by
  have h := ZMod.dft_comp_unitMul (⇑χ) u⁻¹ a
  rw [inv_inv] at h
  have hf : (fun j => χ ((u⁻¹ : (ZMod d)ˣ).val * j)) = ⇑χ := by
    funext j; rw [map_mul, hu, one_mul]
  rw [hf] at h
  rw [h, mul_comm]

/-- **The period identity.** For `γ ∈ Γ₀(32 d²)` and `τ ∈ ℍ` there are `γ'_a ∈ Γ₀(32)` and
`τ'_a ∈ ℍ` (`a ∈ ℤ/d`) with
`d (Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ_d(a) (Φ₁(γ'_a τ'_a) − Φ₁(τ'_a))`: move `[1, a/d; 0, 1]` past `γ`
(Tau Ceti `exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom`) and reindex `a ↦ a D²`. -/
theorem period_identity (d : ℕ) [NeZero d] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (32 * d ^ 2))
    (τ : ℍ) :
    ∃ (γ' : ZMod d → SL(2, ℤ)) (τ' : ZMod d → ℍ), (∀ a, γ' a ∈ Gamma0 32) ∧
      (d : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) =
        ∑ a : ZMod d, 𝓕 (jacobiChar d) a *
          (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ)) := by
  obtain ⟨c, hc, -⟩ := CongruenceSubgroup.exists_eq_mul_mul_of_mem_Gamma0
    (dvd_level_left d) (dvd_level_right d) hγ
  set D : ZMod d := ((γ 1 1 : ℤ) : ZMod d) with hDdef
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hAD : ((γ 0 0 : ℤ) : ZMod d) * D = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod d) hdet
    push_cast [hc, ZMod.natCast_self] at this
    simpa [hDdef] using this
  have hD : IsUnit D := IsUnit.of_mul_eq_one_right _ hAD
  set w : (ZMod d)ˣ := hD.unit with hw
  set v : (ZMod d)ˣ := w ^ 2 with hv
  have hvD : (v : ZMod d) = D ^ 2 := by simp [hv, hw]
  have hχv : jacobiChar d ((v⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
    rw [hv, ← inv_pow, Units.val_pow_eq_pow_val, map_pow]
    exact jacobiChar_sq_unit d _
  have hex : ∀ a : ZMod d, ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 0 0 + (a.val : ℤ) * d * c ∧
      γ' 1 0 = γ 1 0 ∧ γ' 1 1 = γ 1 1 - (((a * D ^ 2).val : ℕ) : ℤ) * d * c ∧
      upperRightHom (((a.val : ℤ) : ℝ) / d) * mapGL ℝ γ =
        mapGL ℝ γ' * upperRightHom (((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) := fun a =>
    TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom γ hc (by
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  choose γ' hγ'0 hγ'1 hγ'2 hγ'eq using hex
  set τ' : ZMod d → ℍ := fun a => ((((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) +ᵥ τ) with hτ'
  refine ⟨γ', τ', fun a => ?_, ?_⟩
  · rw [mem_Gamma0_iff_dvd, hγ'1]
    have := (mem_Gamma0_iff_dvd.mp hγ)
    exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right 32 (d ^ 2))).trans (by exact_mod_cast this)
  -- the translate of `γ τ` by `a/d` is `γ'_a τ'_a`
  have hmove : ∀ a : ZMod d, ((γ • τ : ℍ) : ℂ) + (a.val : ℂ) / d = ((γ' a • τ' a : ℍ) : ℂ) := by
    intro a
    have h := congrArg (fun g : GL (Fin 2) ℝ => g • τ) (hγ'eq a)
    simp only [mul_smul, TauCeti.Matrix.GeneralLinearGroup.upperRightHom_smul] at h
    have h' := congrArg (fun z : ℍ => (z : ℂ)) h
    simp only [UpperHalfPlane.coe_vadd] at h'
    rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
      TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← h']
    push_cast
    ring
  have hz : 0 < ((γ • τ : ℍ) : ℂ).im := (γ • τ).im_pos
  rw [mul_sub, twist_formula d hz, twist_formula d τ.im_pos, ← Finset.sum_sub_distrib]
  -- reindex the second sum by `b = a D²`
  have hre : ∑ b : ZMod d, 𝓕 (jacobiChar d) b * eichlerCd 1 ((τ : ℂ) + (b.val : ℂ) / d) =
      ∑ a : ZMod d, 𝓕 (jacobiChar d) a * eichlerCd 1 ((τ' a : ℍ) : ℂ) := by
    refine (Fintype.sum_equiv (Units.mulRight v) _ _ fun a => ?_).symm
    simp only [Units.mulRight_apply, hτ', UpperHalfPlane.coe_vadd]
    rw [dft_mul_unit d (jacobiChar d) v hχv a, hvD]
    congr 2
    push_cast
    ring
  rw [Finset.sum_sub_distrib, hre, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hmove a, mul_sub]

/-! ## §4. The Gauss sum of `χ_d = (·/d)`: primitivity and `g² = d` -/

/-- For a prime `p ∣ d` (`d` odd squarefree, `d = e p`) there is `U ≡ 1 (mod e)`, coprime to `d`,
with `(U/d) = −1`. -/
theorem exists_unit_jacobi_neg {e p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpe : ¬ p ∣ e)
    (he : e ≠ 0) :
    ∃ t : ℕ, Nat.Coprime (1 + e * t) (e * p) ∧ jacobiSym ((1 + e * t : ℕ) : ℤ) (e * p) = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero e := ⟨he⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have he0 : (e : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff]
  set t : ℕ := ((a - 1) * (e : ZMod p)⁻¹).val with ht
  have hU : ((1 + e * t : ℕ) : ZMod p) = a := by
    push_cast
    rw [ht, ZMod.natCast_zmod_val]
    field_simp
    ring
  have hpU : ¬ p ∣ (1 + e * t) := by
    intro h
    rw [← ZMod.natCast_eq_zero_iff, hU] at h
    exact ha (h ▸ ⟨0, by simp⟩)
  refine ⟨t, ?_, ?_⟩
  · refine Nat.Coprime.mul_right ?_ ?_
    · rw [show 1 + e * t = 1 + t * e by ring, Nat.coprime_add_mul_right_left]
      exact Nat.coprime_one_left e
    · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpU))
  · rw [jacobiSym.mul_right]
    have h1 : jacobiSym ((1 + e * t : ℕ) : ℤ) e = 1 := by
      rw [jacobiSym.mod_left' (a₂ := 1) (by push_cast; rw [Int.add_mul_emod_self_left]),
        jacobiSym.one_left]
    have h2 : jacobiSym ((1 + e * t : ℕ) : ℤ) p = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      rw [Int.cast_natCast, hU]
      exact ha
    rw [h1, h2, one_mul]

/-- **`(·/d)` is a primitive Dirichlet character modulo `d`** for odd squarefree `d`. -/
theorem jacobiChar_isPrimitive {d : ℕ} [NeZero d] (hodd : Odd d) (hsq : Squarefree d) :
    (jacobiChar d).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  set m := (jacobiChar d).conductor with hmdef
  have hm : m ∣ d := DirichletCharacter.conductor_dvd_level _
  by_contra hne
  obtain ⟨k, hk⟩ := hm
  have hk1 : k ≠ 1 := by rintro rfl; exact hne (by rw [hk, mul_one])
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
  obtain ⟨k', rfl⟩ := hpk
  set e := m * k' with hedef
  have hde : d = e * p := by rw [hk, hedef]; ring
  have hd0 : d ≠ 0 := NeZero.ne d
  have he0 : e ≠ 0 := by rintro h; rw [h, zero_mul] at hde; exact hd0 hde
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ d := ⟨e, by rw [hde]; ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hpe : ¬ p ∣ e := by
    rintro ⟨e', he'⟩
    have := hsq p ⟨e', by rw [hde, he']; ring⟩
    exact hp.not_isUnit this
  obtain ⟨t, hcop, hneg⟩ := exists_unit_jacobi_neg hp hp2 hpe he0
  rw [← hde] at hcop hneg
  set u : (ZMod d)ˣ := ZMod.unitOfCoprime (1 + e * t) hcop
  have hmd : m ∣ d := ⟨k' * p, by rw [hk]; ring⟩
  have hfac := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := jacobiChar d) hmd).mp
    (DirichletCharacter.factorsThrough_conductor _)
  have hker : u ∈ (ZMod.unitsMap hmd).ker := by
    rw [MonoidHom.mem_ker]
    ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_ofClass, ZMod.castHom_apply,
      ZMod.coe_unitOfCoprime, ZMod.cast_natCast hmd, Units.val_one]
    push_cast
    rw [show (e : ZMod m) = 0 by
      rw [ZMod.natCast_eq_zero_iff]; exact ⟨k', rfl⟩]
    ring
  have h1 := hfac hker
  rw [MonoidHom.mem_ker, MulChar.toUnitHom_eq] at h1
  have h2 : (jacobiChar d) (u : ZMod d) = 1 := by
    have := congrArg (fun x : ℂˣ => (x : ℂ)) h1
    simpa [MulChar.coe_equivToUnitHom] using this
  rw [ZMod.coe_unitOfCoprime, jacobiChar_natCast, hneg] at h2
  norm_num at h2

theorem jacobiChar_inv_apply (d : ℕ) [NeZero d] (x : ZMod d) :
    (jacobiChar d)⁻¹ x = jacobiChar d x := by
  rw [MulChar.inv_apply_eq_inv', ZInQ.GZTheta.jacobiChar_apply]
  rcases jacobiSym.trichotomy ((x.val : ℕ) : ℤ) d with h | h | h <;> rw [h] <;> norm_num

theorem jacobiChar_neg_one {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) : jacobiChar d (-1) = 1 := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have h : (-1 : ZMod d) = (((d - 1 : ℕ) : ℤ) : ZMod d) := by
    have h1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    push_cast [Nat.cast_sub h1, ZMod.natCast_self]
    ring
  rw [h, Int.cast_natCast, jacobiChar_natCast]
  have : jacobiSym ((d - 1 : ℕ) : ℤ) d = jacobiSym (-1) d := by
    apply jacobiSym.mod_left'
    have h1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    push_cast [Nat.cast_sub h1]
    rw [show (d : ℤ) - 1 = -1 + d * 1 by ring, Int.add_mul_emod_self_left]
  rw [this, jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_one_mod_four hd4]
  simp

/-- The Gauss sum `g = Σ_a (a/d) e(a/d)` of `χ_d`. -/
def gaussD (d : ℕ) [NeZero d] : ℂ := gaussSum (jacobiChar d) ZMod.stdAddChar

/-- `𝓕χ_d = g · χ_d` (`χ_d` primitive, real and even). -/
theorem dft_jacobiChar {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) (a : ZMod d) :
    𝓕 (jacobiChar d) a = jacobiChar d a * gaussD d := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  rw [(jacobiChar_isPrimitive hodd hsq).fourierTransform_eq_inv_mul_gaussSum, jacobiChar_inv_apply,
    neg_eq_neg_one_mul, map_mul, jacobiChar_neg_one hd4, one_mul, gaussD]

/-- **`g² = d`** for squarefree `d ≡ 1 (mod 4)`. -/
theorem gaussD_sq {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    gaussD d ^ 2 = d := by
  have h := congrFun (ZMod.dft_dft (⇑(jacobiChar d))) 1
  have hf : 𝓕 (⇑(jacobiChar d)) = fun a => jacobiChar d a * gaussD d :=
    funext (dft_jacobiChar hd4 hsq)
  rw [hf, ZMod.dft_mul_const] at h
  dsimp only at h
  rw [dft_jacobiChar hd4 hsq, smul_eq_mul,
    neg_eq_neg_one_mul, map_mul, jacobiChar_neg_one hd4, one_mul, map_one] at h
  linear_combination h

/-! ## §5. Scaling a lattice -/

/-- The period pair `(g ω₁, g ω₂)`, `g ≠ 0`. -/
def scalePP (L : PeriodPair) (g : ℂ) (hg : g ≠ 0) : PeriodPair where
  ω₁ := g * L.ω₁
  ω₂ := g * L.ω₂
  indep := by
    have hinj : Function.Injective (LinearMap.mulLeft ℝ g : ℂ →ₗ[ℝ] ℂ) := fun x y h => by
      simpa [hg] using h
    have := L.indep.map' (LinearMap.mulLeft ℝ g) (LinearMap.ker_eq_bot.mpr hinj)
    convert this using 1
    ext i
    fin_cases i <;> simp

theorem mem_scalePP {L : PeriodPair} {g : ℂ} (hg : g ≠ 0) {x : ℂ} :
    x ∈ (scalePP L g hg).lattice ↔ ∃ y ∈ L.lattice, x = g * y := by
  simp only [PeriodPair.mem_lattice, scalePP]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m * L.ω₁ + n * L.ω₂, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

theorem G_scalePP (L : PeriodPair) {g : ℂ} (hg : g ≠ 0) (n : ℕ) :
    (scalePP L g hg).G n = (g ^ n)⁻¹ * L.G n := by
  let e : L.lattice ≃ (scalePP L g hg).lattice :=
    { toFun := fun l => ⟨g * l, (mem_scalePP hg).mpr ⟨l, l.2, rfl⟩⟩
      invFun := fun l => ⟨g⁻¹ * l, by
        obtain ⟨y, hy, hl⟩ := (mem_scalePP hg).mp l.2
        rw [hl, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]; exact hy⟩
      left_inv := fun l => by ext; simp [hg]
      right_inv := fun l => by ext; simp [hg] }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq, ← tsum_mul_left]
  congr 1
  funext l
  simp only [e, Equiv.coe_fn_mk]
  rw [mul_pow, mul_inv]

theorem g₂_scalePP (L : PeriodPair) {g : ℂ} (hg : g ≠ 0) :
    (scalePP L g hg).g₂ = (g ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_scalePP]; ring

theorem g₃_scalePP (L : PeriodPair) {g : ℂ} (hg : g ≠ 0) :
    (scalePP L g hg).g₃ = (g ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_scalePP]; ring

/-- `L` is a period lattice of `C_d : y² = x³ − d²x` iff `g₂(L) = 4d²`, `g₃(L) = 0`. -/
theorem isPeriodLattice_cd_iff (d : ℕ) (L : PeriodPair) :
    ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L ↔
      L.g₂ = 4 * (d : ℂ) ^ 2 ∧ L.g₃ = 0 := by
  simp only [ZInQ.GZHL3.IsPeriodLattice, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.baseChange,
    WeierstrassCurve.map, shortCurve]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, ?_⟩ <;> [rw [h1]; rw [h2]; rw [h1]; rw [h2]] <;>
    ring

/-! ## §6. The level-32 leaf and the reduction -/

/-- `C₁ : y² = x³ − x`, i.e. `C_d` for `d = 1` (Cremona `32a2`). -/
abbrev curveC1 : WeierstrassCurve ℚ := shortCurve (-((1 : ℕ) : ℚ) ^ 2)

/-- **(LEAF, level 32) The modular parametrization of `C₁ : y² = x³ − x` by `X₀(32)`, in analytic
form, with rational Manin constant.** Let `Φ₁(τ) = Σ_{n ≥ 1} aₙ/n qⁿ` be the Eichler integral of
the weight-2 newform `f₁ = Σ aₙ qⁿ = η(4τ)²η(8τ)²` of level 32 (`aₙ = heckeCoeff 1 n`, the
coefficients of the Hecke character of `ℚ(i)` attached to `C₁`; `aₙ = aₙ(C₁)` is Deuring's
theorem, proved in the kernel). For every period lattice `L` of `C₁` (`g₂(L) = 4`, `g₃(L) = 0`)
there is `c ∈ ℚ^×` with `c (Φ₁(γτ) − Φ₁(τ)) ∈ L` for all `γ ∈ Γ₀(32)`, `τ ∈ ℍ`: the map
`τ ↦ weierPt C₁ L (c Φ₁(τ))` factors through `X₀(32)`, i.e. `c Λ_{f₁} ⊆ L`.

This is `GZHL3.EichlerShimuraParamAt C₁` at the level-32 newform (`modularParamC1_of_leaves`
derives it from gz-hl3's `StrongWeilCurve`, `IsogenyLattice`, `WeierstrassUniformization`):
Eichler–Shimura for the one newform of level 32, with `X₀(32) = 32a1` (genus one) and the explicit
2-isogeny `32a1 → 32a2 = C₁` (x0-32, `TYZGenus/X0.lean` §4–§10). Sources: Shimura 1971, Thm 7.14
(UNVERIFIED number); Cremona, *Algorithms for modular elliptic curves*, Table 1 (32a1 optimal,
Manin constant 1; UNVERIFIED locator). -/
def ModularParamC1 : Prop :=
  ∀ L : PeriodPair, ZInQ.GZHL3.IsPeriodLattice curveC1 L → ∃ c : ℚ, c ≠ 0 ∧
    ∀ γ ∈ Gamma0 32, ∀ τ : ℍ, (c : ℂ) * (eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) ∈
      L.lattice

theorem gaussD_ne_zero {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    gaussD d ≠ 0 := by
  intro h
  have := gaussD_sq hd4 hsq
  rw [h] at this
  norm_num at this
  exact NeZero.ne d (by exact_mod_cast this.symm)

/-- **The twist step.** `ModularParamC1` gives the analytic modular parametrization of every
`C_d`, `d ≡ 1 (mod 4)` squarefree, at the Eichler integral `Φ_d` and level `32 d²`. -/
theorem periods_cd (h : ModularParamC1) {d : ℕ} [NeZero d] (hd4 : d % 4 = 1)
    (hsq : Squarefree d) (L : PeriodPair)
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ γ ∈ Gamma0 (32 * d ^ 2), ∀ τ : ℍ,
      (c : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) ∈ L.lattice := by
  set g := gaussD d with hgdef
  have hg : g ≠ 0 := gaussD_ne_zero hd4 hsq
  have hg2 : g ^ 2 = d := gaussD_sq hd4 hsq
  obtain ⟨h2, h3⟩ := (isPeriodLattice_cd_iff d L).mp hL
  have hL' : ZInQ.GZHL3.IsPeriodLattice curveC1 (scalePP L g hg) := by
    rw [isPeriodLattice_cd_iff, g₂_scalePP, g₃_scalePP, h2, h3]
    refine ⟨?_, by ring⟩
    have : g ^ 4 = (d : ℂ) ^ 2 := by rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, hg2]
    rw [this]
    have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
    field_simp
    push_cast; ring
  obtain ⟨c, hc, hper⟩ := h _ hL'
  refine ⟨c, hc, fun γ hγ τ => ?_⟩
  obtain ⟨γ', τ', hγ', heq⟩ := period_identity d hγ τ
  have hm : ∀ a : ZMod d, ∃ m ∈ L.lattice, (c : ℂ) *
      (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ)) = g * m :=
    fun a => (mem_scalePP hg).mp (hper (γ' a) (hγ' a) (τ' a))
  choose m hmL hmeq using hm
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have key : (c : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) =
      ∑ a : ZMod d, ((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * m a := by
    have e1 : (c : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) =
        (d : ℂ)⁻¹ * ((c : ℂ) * ((d : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)))) := by
      field_simp
    rw [e1, heq, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dft_jacobiChar hd4 hsq, ZInQ.GZTheta.jacobiChar_apply]
    calc (d : ℂ)⁻¹ * ((c : ℂ) * (((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * g *
          (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ))))
        = (d : ℂ)⁻¹ * (((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * g *
          ((c : ℂ) * (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ)))) := by ring
      _ = (d : ℂ)⁻¹ * (((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * (g ^ 2) * m a) := by
          rw [hmeq a]; ring
      _ = _ := by rw [hg2]; field_simp
  rw [key]
  refine Submodule.sum_mem _ fun a _ => ?_
  have := Submodule.smul_mem L.lattice (jacobiSym ((a.val : ℕ) : ℤ) d) (hmL a)
  rwa [zsmul_eq_mul] at this

/-! ## §7. `ShimuraCMParamCd` (gz-hl3) from the level-32 leaf -/

/-- For a newform `f` of `C_d` the Eichler integral is `Φ_d`. -/
theorem eichler_eq_eichlerCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : HeckeRing.GL2.Newform N 2)
    (hf : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ))
    (τ : ℍ) : ZInQ.GZHL3.eichler f τ = eichlerCd d (τ : ℂ) := by
  unfold ZInQ.GZHL3.eichler eichlerCd
  congr 1
  funext n
  rw [hf (n + 1) (Nat.succ_ne_zero n),
    ZInQ.GZStatements.LFunction_cd_eq_heckeCoeff hd4 hsq (Nat.succ_ne_zero n)]

/-- **The analytic modular parametrization of `C_d`** (`d ≡ 1 mod 4` squarefree) from the
level-32 leaf: the newform has level `32 d²` (`GZStatements.level_eq_of_coeff_cd`), its Eichler
integral is `Φ_d` (Deuring, proved), and `periods_cd`. -/
theorem eichlerShimuraParamAt_cd (h : ModularParamC1) {d : ℕ} (hd4 : d % 4 = 1)
    (hsq : Squarefree d) : ZInQ.GZHL3.EichlerShimuraParamAt (shortCurve (-(d : ℚ) ^ 2)) := by
  intro N _ f hχ hf L hL
  have : NeZero d := ⟨by omega⟩
  have hN := ZInQ.GZStatements.level_eq_of_coeff_cd hd4 hsq f hχ hf
  subst hN
  obtain ⟨c, hc, hper⟩ := periods_cd h hd4 hsq L hL
  refine ⟨c, hc, fun γ hγ τ => ?_⟩
  rw [eichler_eq_eichlerCd hd4 hsq f hf, eichler_eq_eichlerCd hd4 hsq f hf]
  exact hper γ hγ τ

/-- **gz-hl3's `ShimuraCMParamCd` from the single level-32 leaf `ModularParamC1`.** -/
theorem shimuraCMParamCd_of_modularParamC1 (h : ModularParamC1) :
    ZInQ.GZHL3.ShimuraCMParamCd := fun d hd hsq =>
  eichlerShimuraParamAt_cd h (by omega) hsq

/-! ## §8. `ModularParamC1` is no stronger than gz-hl3's leaves -/

/-- `ModularParamC1` is `EichlerShimuraParamAt C₁` at the level-32 newform. -/
theorem modularParamC1_of_eichlerShimuraParamAt
    (h : ZInQ.GZHL3.EichlerShimuraParamAt curveC1) : ModularParamC1 := by
  intro L hL
  obtain ⟨_, g, hgχ, hg⟩ := ZInQ.GZStatements.exists_newform_level32 (d := 1) (by norm_num)
    squarefree_one
  have hgf : ∀ n : ℕ, n ≠ 0 → coeff g n = (curveC1.LFunction n : ℂ) := fun n hn => by
    rw [hg n hn, ← ZInQ.GZStatements.LFunction_cd_eq_heckeCoeff (d := 1) (by norm_num)
      squarefree_one hn]
  obtain ⟨c, hc, hcL⟩ := h (32 * 1 ^ 2) g hgχ hgf L hL
  refine ⟨c, hc, fun γ hγ τ => ?_⟩
  have hγ' : γ ∈ Gamma0 (32 * 1 ^ 2) := by simpa using hγ
  have := hcL γ hγ' τ
  rwa [eichler_eq_eichlerCd (d := 1) (by norm_num) squarefree_one g hgf,
    eichler_eq_eichlerCd (d := 1) (by norm_num) squarefree_one g hgf] at this

/-- **`ModularParamC1` follows from gz-hl3's leaves** (so it is no stronger than them). -/
theorem modularParamC1_of_leaves (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hSW : ZInQ.GZHL3.StrongWeilCurve) (hI : ZInQ.GZHL3.IsogenyLattice) : ModularParamC1 := by
  have : curveC1.IsElliptic := shortCurve_cd_isElliptic (by norm_num)
  exact modularParamC1_of_eichlerShimuraParamAt
    (ZInQ.GZHL3.eichlerShimuraParamAt_of_leaves hU hSW hI curveC1)

/-- **`GZStatements.GrossZagierHeegnerCd` from the level-32 leaf and the four Heegner-point
leaves** (no `StrongWeilCurve`, no `IsogenyLattice`). -/
theorem grossZagierHeegnerCd_of_leaves (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hP : ModularParamC1) (hHP : ZInQ.GZHL3.HeegnerPointRationalCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  ZInQ.GZHL3.grossZagierHeegnerCd_of_leaves hU (shimuraCMParamCd_of_modularParamC1 hP) hHP hGZ hGC

end ZInQ.GZWeil

#print axioms ZInQ.GZWeil.shimuraCMParamCd_of_modularParamC1
#print axioms ZInQ.GZWeil.modularParamC1_of_leaves
#print axioms ZInQ.GZWeil.grossZagierHeegnerCd_of_leaves
