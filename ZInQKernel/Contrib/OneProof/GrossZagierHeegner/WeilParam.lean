import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Weil
import ZInQKernel.Contrib.TYZGenus.ShimuraThetaDup
import ZInQKernel.Contrib.GZTheta.EtaForm32
import ZInQKernel.Contrib.GZTheta.EtaTheta

/-!
# gz-weil: the modular parametrization of `C₁` by `X₀(32)` from x0-32's eta-quotient identity

Task gz-weil (2026-11-15). Report: `docs/research/gz-weil.md`; scratch and log: `scratch/gz-weil/`.

`ModularParamC1` (`Weil.lean`: the periods of `Φ₁ = Σ heckeCoeff 1 n / n · qⁿ` over `Γ₀(32)` lie in
`c L` for every lattice `L` of `C₁ : y² = x³ − x`, `c ∈ ℚ^×`) is proved here from one identity of
eta quotients, x0-32's `X0.EtaModelDifferential`: on the eta-quotient model
`x = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) + 2`, `y = −η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴)` of
`X₀(32) = 32a1 : y² = x³ + 4x`, `x'(τ) = 4πi f₁(τ) y(τ)` (`dx/2y = 2πi f₁ dτ`). The proof:

* C1 `Φ₁' = 2πi f₁` (termwise differentiation; gz-theta's `etaThetaIdentity`);
* C3 `Φ₁(γτ) − Φ₁(τ)` is constant for `γ ∈ Γ₀(32)` (`f₁` has weight 2: gz-theta's `etaQuot32_slash_eq`);
* C4 `℘_L : ℂ ∖ L → ℂ` is surjective (open mapping, compact fundamental domain, poles);
* C5 for a lattice `L` of `32a1` and `℘(z₀) = x(τ₀)`, `℘'(z₀) = 2y(τ₀)`: `x = ℘(Φ₁ + c₀)` near `τ₀`
  (`Ψ = ℘(Φ₁ + c₀) − x` satisfies `Ψ' = hΨ`, `Ψ(τ₀) = 0`; order of vanishing);
* C6 `x = ℘(Φ₁ + c₀)` on all of `ℍ` (clopen argument; `℘ → ∞` at lattice points);
* C7 `x(γτ) = x(τ)` (tyz-cm's `etaModelInvariant`) then gives `℘(u + ω) = ℘(u)` on an open set,
  `ω = Φ₁(γτ) − Φ₁(τ)`, hence `ω ∈ L` (identity theorem; pole at `0`);
* C8 the lattices `((1 ± i)/2) L` of `32a1`, for `L` a lattice of `C₁`, give `2 Λ_{f₁} ⊆ L`.

The curve equation `y² = x³ + 4x` (tyz-cm's `etaModelEquation`) and the invariance are proved in
the kernel; the only input here is `X0.EtaModelDifferential`, which `WeilTheta.lean` and
`WeilJacobi.lean` prove. No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane CongruenceSubgroup Complex
open ZInQ.Contrib.HeckeFE
open scoped MatrixGroups

namespace ZInQ.GZWeil

theorem norm_exp_term (n : ℕ) (z : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ =
      Real.exp (-2 * Real.pi * z.im) ^ (n + 1) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat]
  push_cast
  ring

theorem summable_poly_geom {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ((2 * (n : ℝ) + 3) ^ 3) * r ^ n := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_of_nonneg hr0]; exact hr1
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hn
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 hn
  have := (((h3.mul_left 8).add (h2.mul_left 36)).add (h1.mul_left 54)).add (h0.mul_left 27)
  refine this.congr fun n => ?_
  ring

/-! ## C1. `Φ₁' = 2πi f₁` on `ℍ` -/

theorem hasDerivAt_eichler_term (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w))
      (heckeCoeff 1 (n + 1) * (2 * Real.pi * Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)) z := by
  have hn : ((n : ℂ) + 1) ≠ 0 := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero n
  have h1 : HasDerivAt (fun w => 2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w)
      (2 * Real.pi * Complex.I * ((n : ℂ) + 1)) z := by
    simpa using (hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I * ((n : ℂ) + 1))
  have h2 := (h1.cexp).const_mul (heckeCoeff 1 (n + 1) / ((n : ℂ) + 1))
  convert h2 using 1
  field_simp

/-- **`Φ₁'(τ) = 2πi f₁(τ)`**, `f₁ = η(4τ)²η(8τ)²` (termwise differentiation and gz-theta's
`etaThetaIdentity`). -/
theorem hasDerivAt_eichlerCd_one {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (eichlerCd 1) (2 * Real.pi * Complex.I * ZInQ.Contrib.TYZGenus.X0.fC z) z := by
  set ε := z.im / 2 with hε
  have hε0 : 0 < ε := by positivity
  set r : ℝ := Real.exp (-2 * Real.pi * ε) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
  set t : Set ℂ := {w | ε < w.im} with ht
  have htopen : IsOpen t := isOpen_lt continuous_const Complex.continuous_im
  have htconv : Convex ℝ t := convex_halfSpace_im_gt ε
  have hzt : z ∈ t := by show ε < z.im; linarith
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ t →
      ‖heckeCoeff 1 (n + 1) * (2 * Real.pi * Complex.I) *
        Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * w)‖ ≤
        2 * Real.pi * ((2 * (n : ℝ) + 3) ^ 3 * r ^ n) := by
    intro n w hw
    rw [norm_mul, norm_mul, norm_exp_term]
    have hb := norm_heckeCoeff_le 1 (n + 1)
    push_cast at hb
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi]
    have hexp : Real.exp (-2 * Real.pi * w.im) ^ (n + 1) ≤ r ^ n := by
      have h1 : Real.exp (-2 * Real.pi * w.im) ≤ r := by
        rw [hr]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, show ε < w.im from hw])
      calc Real.exp (-2 * Real.pi * w.im) ^ (n + 1) ≤ r ^ (n + 1) :=
            pow_le_pow_left₀ (Real.exp_pos _).le h1 _
        _ ≤ r ^ n := pow_le_pow_of_le_one hr0 hr1.le (Nat.le_succ n)
    have : (2 * ((n : ℝ) + 1) + 1) = 2 * (n : ℝ) + 3 := by ring
    rw [this] at hb
    calc ‖heckeCoeff 1 (n + 1)‖ * (2 * Real.pi) * Real.exp (-2 * Real.pi * w.im) ^ (n + 1)
        ≤ (2 * (n : ℝ) + 3) ^ 3 * (2 * Real.pi) * r ^ n := by gcongr
      _ = _ := by ring
  have hsum0 : Summable fun n : ℕ => heckeCoeff 1 (n + 1) / ((n : ℂ) + 1) *
      Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z) := by
    refine Summable.of_norm_bounded ((summable_poly_geom hr0 hr1).mul_left (2 * Real.pi)) ?_
    intro n
    have h := hbound n z hzt
    rw [norm_mul, norm_mul] at h
    rw [norm_mul, norm_div]
    have hn1 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; push_cast; ring
    have h2pi : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi] at h
    rw [hn1]
    have hpos : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hA : 0 ≤ ‖heckeCoeff 1 (n + 1)‖ * ‖Complex.exp (2 * Real.pi * Complex.I *
        ((n : ℂ) + 1) * z)‖ := by positivity
    calc ‖heckeCoeff 1 (n + 1)‖ / ((n : ℝ) + 1) *
          ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖
        ≤ ‖heckeCoeff 1 (n + 1)‖ * ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ := by
          rw [div_mul_eq_mul_div]
          exact div_le_self hA hpos
      _ ≤ ‖heckeCoeff 1 (n + 1)‖ * (2 * Real.pi) *
          ‖Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) + 1) * z)‖ := by
          nlinarith
      _ ≤ _ := h
  have hD := hasDerivAt_tsum_of_isPreconnected
    ((summable_poly_geom hr0 hr1).mul_left (2 * Real.pi)) htopen htconv.isPreconnected
    (fun n w _ => hasDerivAt_eichler_term n w) hbound hzt hsum0 hzt
  convert hD using 1
  · rfl
  -- the derivative series is `2πi f₁(z)`
  set τ : ℍ := ⟨z, hz⟩
  have hf := ZInQ.GZTheta.etaThetaIdentity τ
  rw [← hasSum_nat_add_iff' 1] at hf
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at hf
  have h0 : heckeCoeff 1 0 = 0 := by
    simp [heckeCoeff, normFiber, gz, Finset.sum_filter]
  rw [h0, sub_zero] at hf
  have hfC : ZInQ.Contrib.TYZGenus.X0.fC z = ModularForm.eta (4 * (τ : ℂ)) ^ 2 * ModularForm.eta (8 * (τ : ℂ)) ^ 2 := rfl
  rw [hfC, ← hf.tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  rw [← Complex.exp_nat_mul]
  push_cast
  ring_nf
  rfl

/-! ## C3. `Φ₁(γτ) − Φ₁(τ)` is constant for `γ ∈ Γ₀(32)` -/

/-- The Möbius map of `γ` on `ℂ`. -/
def moeb (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) / (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ))

theorem coe_smul_eq_moeb (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = moeb γ τ := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, moeb]
  simp

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
    add_zero, Complex.zero_im] at him
  have hc : (γ 1 0 : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h1 | h1
    · exact h1
    · exact absurd h1 hz.ne'
  have hc' : γ 1 0 = 0 := by exact_mod_cast hc
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hc,
    zero_mul, sub_zero, zero_add, Complex.zero_re] at hre
  have hd : γ 1 1 = 0 := by exact_mod_cast hre
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  simp only [hc', hd, mul_zero, sub_zero] at hdet
  exact absurd hdet (by norm_num)

theorem hasDerivAt_moeb (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (moeb γ) (1 / (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ 2) z := by
  have hden := denom_ne_zero' γ hz
  have h1 : HasDerivAt (fun w => ((γ 0 0 : ℤ) : ℂ) * w + ((γ 0 1 : ℤ) : ℂ)) ((γ 0 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)
  have h2 : HasDerivAt (fun w => ((γ 1 0 : ℤ) : ℂ) * w + ((γ 1 1 : ℤ) : ℂ)) ((γ 1 0 : ℤ) : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)
  have h := h1.div h2 hden
  convert h using 2
  · funext w; rfl
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hdetC : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) - ((γ 0 1 : ℤ) : ℂ) * ((γ 1 0 : ℤ) : ℂ) = 1 := by
    exact_mod_cast hdet
  linear_combination -hdetC

theorem im_moeb_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (moeb γ z).im := by
  have := (γ • (⟨z, hz⟩ : ℍ)).im_pos
  rwa [UpperHalfPlane.im, coe_smul_eq_moeb] at this

/-- `f₁(γτ) = (cτ + d)² f₁(τ)` for `γ ∈ Γ₀(32)` (gz-theta's `etaQuot32_slash_eq`). -/
theorem fC_moeb {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) {z : ℂ} (hz : 0 < z.im) :
    ZInQ.Contrib.TYZGenus.X0.fC (moeb γ z) =
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) ^ 2 * ZInQ.Contrib.TYZGenus.X0.fC z := by
  set τ : ℍ := ⟨z, hz⟩
  have h := congrFun (ZInQ.GZTheta.etaQuot32_slash_eq hγ) τ
  rw [ModularForm.SL_slash_def] at h
  simp only at h
  have hden : UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
    rw [UpperHalfPlane.denom]
    simp [τ]
  rw [hden] at h
  have hne := denom_ne_zero' γ hz
  have e1 : ZInQ.Contrib.TYZGenus.X0.fC (moeb γ z) = ZInQ.GZTheta.etaQuot32 (γ • τ) := by
    rw [ZInQ.GZTheta.etaQuot32, coe_smul_eq_moeb]; rfl
  have e2 : ZInQ.Contrib.TYZGenus.X0.fC z = ZInQ.GZTheta.etaQuot32 τ := rfl
  rw [e1, e2, ← h, zpow_neg, zpow_ofNat]
  field_simp

/-- **`Φ₁(γτ) − Φ₁(τ)` does not depend on `τ`** (`γ ∈ Γ₀(32)`): its derivative
`2πi (f₁(γτ)(cτ + d)⁻² − f₁(τ))` vanishes. -/
theorem period_const {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) (τ τ' : ℍ) :
    eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 τ = eichlerCd 1 ((γ • τ' : ℍ) : ℂ) - eichlerCd 1 τ' := by
  rw [coe_smul_eq_moeb, coe_smul_eq_moeb]
  set U : Set ℂ := {w | 0 < w.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hd : ∀ w ∈ U, HasDerivAt (fun w => eichlerCd 1 (moeb γ w) - eichlerCd 1 w) 0 w := by
    intro w hw
    have h1 := (hasDerivAt_eichlerCd_one (im_moeb_pos γ hw)).comp w (hasDerivAt_moeb γ hw)
    have h2 := hasDerivAt_eichlerCd_one hw
    convert h1.sub h2 using 1
    · funext v; rfl
    rw [fC_moeb hγ hw]
    have hne := denom_ne_zero' γ hw
    field_simp
    ring
  exact hUo.is_const_of_deriv_eq_zero hUc (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hd w hw).deriv) τ.im_pos τ'.im_pos

/-! ## C4. `℘` is surjective -/

section Surj

variable (L : PeriodPair)

theorem countable_lattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

theorem isConnected_compl_lattice : IsConnected (L.lattice : Set ℂ)ᶜ :=
  Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_lattice L)

theorem tendsto_weierstrassP_cobounded {l : ℂ} (hl : l ∈ L.lattice) :
    Filter.Tendsto L.weierstrassP (nhdsWithin l {l}ᶜ) (Bornology.cobounded ℂ) :=
  tendsto_cobounded_of_meromorphicOrderAt_neg (by rw [L.order_weierstrassP l hl]; decide)

theorem weierstrassP_not_const : ¬ ∃ c : ℂ, ∀ z ∈ (L.lattice : Set ℂ)ᶜ, L.weierstrassP z = c := by
  rintro ⟨c, hc⟩
  have h0 : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hev : L.weierstrassP =ᶠ[nhdsWithin 0 {0}ᶜ] fun _ => c := by
    have hn := L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)) hn, self_mem_nhdsWithin] with z hz hz0
    refine hc z fun hzL => hz ⟨hzL, hz0⟩
  have hT := tendsto_weierstrassP_cobounded L h0
  have hT' : Filter.Tendsto (fun _ : ℂ => c) (nhdsWithin 0 {0}ᶜ) (Bornology.cobounded ℂ) :=
    hT.congr' hev
  have hb : Filter.Tendsto (fun _ : ℂ => ‖c‖) (nhdsWithin (0 : ℂ) {0}ᶜ) Filter.atTop := by
    simpa [← tendsto_norm_atTop_iff_cobounded] using hT'
  exact Filter.not_tendsto_const_atTop _ _ hb

/-- **`℘_L : ℂ ∖ L → ℂ` is surjective**: its image is open (open mapping) and closed (reduce to
the compact closure of a fundamental domain; `℘ → ∞` at the lattice points). -/
theorem weierstrassP_surjective (w : ℂ) : ∃ z ∉ L.lattice, L.weierstrassP z = w := by
  set V := L.weierstrassP '' (L.lattice : Set ℂ)ᶜ with hV
  have hUo : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hopen : IsOpen V := by
    rcases L.analyticOnNhd_weierstrassP.is_constant_or_isOpen
      (isConnected_compl_lattice L).isPreconnected with h | h
    · exact absurd h (weierstrassP_not_const L)
    · exact h _ subset_rfl hUo
  have hclosed : IsClosed V := by
    rw [← closure_subset_iff_isClosed]
    intro v hv
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hv
    choose z hz hzu using hu
    set b := L.basis
    have hspan : Submodule.span ℤ (Set.range b) = L.lattice := L.lattice_eq_span_range_basis.symm
    set p : ℕ → ℂ := fun n => ZSpan.fract b (z n) with hp
    have hpz : ∀ n, L.weierstrassP (p n) = u n := by
      intro n
      have hmem : ((ZSpan.floor b (z n) : Submodule.span ℤ (Set.range b)) : ℂ) ∈ L.lattice := by
        rw [← hspan]; exact (ZSpan.floor b (z n)).2
      rw [hp]
      simp only [ZSpan.fract_apply]
      rw [← hzu n]
      exact L.weierstrassP_sub_coe (z n) ⟨_, hmem⟩
    have hpL : ∀ n, p n ∉ L.lattice := by
      intro n hpn
      apply hz n
      have hmem : ((ZSpan.floor b (z n) : Submodule.span ℤ (Set.range b)) : ℂ) ∈ L.lattice := by
        rw [← hspan]; exact (ZSpan.floor b (z n)).2
      have : z n = p n + ((ZSpan.floor b (z n) : Submodule.span ℤ (Set.range b)) : ℂ) := by
        rw [hp]; simp only [ZSpan.fract_apply]; ring
      rw [this]; exact add_mem hpn hmem
    have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
      (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
    obtain ⟨q, -, φ, hφ, htend⟩ := hK.tendsto_subseq
      (fun n => subset_closure (ZSpan.fract_mem_fundamentalDomain b (z n)))
    have hu' : Filter.Tendsto (fun k => L.weierstrassP (p (φ k))) Filter.atTop (nhds v) := by
      simp only [hpz]; exact hlim.comp hφ.tendsto_atTop
    by_cases hq : q ∈ L.lattice
    · exfalso
      have hw : Filter.Tendsto (fun k => p (φ k)) Filter.atTop (nhdsWithin q {q}ᶜ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨htend, Filter.Eventually.of_forall fun k => ?_⟩
        intro h
        exact hpL (φ k) (h ▸ hq)
      have hc := (tendsto_weierstrassP_cobounded L hq).comp hw
      rw [← tendsto_norm_atTop_iff_cobounded] at hc
      exact not_tendsto_atTop_of_tendsto_nhds (hu'.norm) hc
    · have hcont : ContinuousAt L.weierstrassP q := (L.analyticOnNhd_weierstrassP q hq).continuousAt
      have := tendsto_nhds_unique (hcont.tendsto.comp htend) hu'
      exact ⟨q, hq, this⟩
  have hne : V.Nonempty := ⟨_, L.ω₁ / 2, L.ω₁_div_two_notMem_lattice, rfl⟩
  have huniv := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hne)
  have hw : w ∈ V := huniv ▸ Set.mem_univ w
  obtain ⟨z, hz, hzw⟩ := hw
  exact ⟨z, hz, hzw⟩

end Surj

/-! ## C5–C7. `x(τ) = ℘(Φ₁(τ) + c₀)` and the periods of `Φ₁` lie in `L` -/

section Param

open ZInQ.Contrib.TYZGenus Filter Topology

variable (L : PeriodPair) (hg2 : L.g₂ = -16) (hg3 : L.g₃ = 0)

include hg2 hg3 in
theorem relation_A {z : ℂ} (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 + 16 * L.weierstrassP z := by
  rw [L.derivWeierstrassP_sq z hz, hg2, hg3]; ring

theorem U_open : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im

theorem hasDerivAt_wp {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  rwa [L.deriv_weierstrassP] at this

theorem analyticAt_eichler {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ (eichlerCd 1) σ := by
  have hd : DifferentiableOn ℂ (eichlerCd 1) {w : ℂ | 0 < w.im} := fun w hw =>
    (hasDerivAt_eichlerCd_one hw).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (U_open.mem_nhds hσ)

theorem analyticAt_xC {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ X0.xC σ := by
  have hd : DifferentiableOn ℂ X0.xC {w : ℂ | 0 < w.im} := fun w hw =>
    (X0.differentiableAt_xC ⟨w, hw⟩).differentiableWithinAt
  exact hd.analyticAt (U_open.mem_nhds hσ)

theorem analyticAt_yC {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ X0.yC σ := by
  have hd : DifferentiableOn ℂ X0.yC {w : ℂ | 0 < w.im} := fun w hw =>
    (X0.differentiableAt_yC ⟨w, hw⟩).differentiableWithinAt
  exact hd.analyticAt (U_open.mem_nhds hσ)

theorem analyticAt_fC {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ X0.fC σ := by
  have hd : DifferentiableOn ℂ X0.fC {w : ℂ | 0 < w.im} := fun w hw =>
    (X0.differentiableAt_fC ⟨w, hw⟩).differentiableWithinAt
  exact hd.analyticAt (U_open.mem_nhds hσ)

include hg2 hg3 in
/-- **Local identity (C5).** If `℘(z₀) = x(τ₀)` and `℘'(z₀) = 2y(τ₀)`, then `℘(Φ₁(σ) + c₀) = x(σ)`
near `τ₀`, `c₀ = z₀ − Φ₁(τ₀)`: `Ψ = ℘(Φ₁ + c₀) − x` satisfies `Ψ' = h Ψ` with `h` analytic and
`Ψ(τ₀) = 0`, so its order of vanishing is infinite. -/
theorem local_eq (hD : X0.EtaModelDifferential) (τ0 : ℍ) {z0 : ℂ} (hz0 : z0 ∉ L.lattice)
    (hx : L.weierstrassP z0 = X0.xC τ0) (hy : L.derivWeierstrassP z0 = 2 * X0.yC τ0) :
    ∀ᶠ σ in 𝓝 (τ0 : ℂ),
      L.weierstrassP (eichlerCd 1 σ + (z0 - eichlerCd 1 τ0)) = X0.xC σ := by
  set c0 := z0 - eichlerCd 1 τ0 with hc0
  set w : ℂ → ℂ := fun σ => eichlerCd 1 σ + c0 with hw
  have hwτ : w τ0 = z0 := by simp [hw, hc0]
  set Ψ : ℂ → ℂ := fun σ => L.weierstrassP (w σ) - X0.xC σ with hΨ
  have hτ0 : 0 < (τ0 : ℂ).im := τ0.im_pos
  have hwa : AnalyticAt ℂ w τ0 := (analyticAt_eichler hτ0).add analyticAt_const
  have hwc : ContinuousAt w τ0 := hwa.continuousAt
  have hΨa : AnalyticAt ℂ Ψ τ0 :=
    ((L.analyticOnNhd_weierstrassP _ (hwτ ▸ hz0)).comp hwa).sub (analyticAt_xC hτ0)
  have hΨ0 : Ψ τ0 = 0 := by simp [hΨ, hwτ, hx]
  -- eventually: `σ ∈ ℍ`, `w σ ∉ L`, `℘'(w σ) + 2 y(σ) ≠ 0`
  have hevU : ∀ᶠ σ in 𝓝 (τ0 : ℂ), 0 < σ.im := U_open.mem_nhds hτ0
  have hevL : ∀ᶠ σ in 𝓝 (τ0 : ℂ), w σ ∉ L.lattice :=
    hwc.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds (hwτ ▸ hz0))
  have hy0 : X0.yC τ0 ≠ 0 := X0.yC_ne_zero τ0
  have hden_c : ContinuousAt (fun σ => L.derivWeierstrassP (w σ) + 2 * X0.yC σ) τ0 := by
    refine ContinuousAt.add ?_ ((analyticAt_yC hτ0).continuousAt.const_mul 2)
    exact ContinuousAt.comp_of_eq (g := L.derivWeierstrassP) (f := w)
      (L.analyticOnNhd_derivWeierstrassP _ (hwτ ▸ hz0)).continuousAt hwc hwτ
  have hden0 : L.derivWeierstrassP (w τ0) + 2 * X0.yC τ0 ≠ 0 := by
    rw [hwτ, hy]; intro h; apply hy0; linear_combination h / 4
  have hevD : ∀ᶠ σ in 𝓝 (τ0 : ℂ), L.derivWeierstrassP (w σ) + 2 * X0.yC σ ≠ 0 :=
    hden_c.eventually_ne hden0
  set h : ℂ → ℂ := fun σ => 2 * Real.pi * Complex.I * X0.fC σ *
    (4 * (L.weierstrassP (w σ) ^ 2 + L.weierstrassP (w σ) * X0.xC σ + X0.xC σ ^ 2 + 4)) /
      (L.derivWeierstrassP (w σ) + 2 * X0.yC σ) with hh
  have hha : AnalyticAt ℂ h τ0 := by
    have hpw : AnalyticAt ℂ (fun σ => L.weierstrassP (w σ)) τ0 :=
      (L.analyticOnNhd_weierstrassP _ (hwτ ▸ hz0)).comp hwa
    have hpw' : AnalyticAt ℂ (fun σ => L.derivWeierstrassP (w σ)) τ0 :=
      (L.analyticOnNhd_derivWeierstrassP _ (hwτ ▸ hz0)).comp hwa
    have hxa := analyticAt_xC hτ0
    have hya := analyticAt_yC hτ0
    have hfa := analyticAt_fC hτ0
    refine AnalyticAt.div ?_ (hpw'.add (analyticAt_const.mul hya)) hden0
    exact (((analyticAt_const.mul hfa)).mul
      (analyticAt_const.mul ((((hpw.pow 2).add (hpw.mul hxa)).add (hxa.pow 2)).add analyticAt_const)))
  have hderiv : deriv Ψ =ᶠ[𝓝 (τ0 : ℂ)] h * Ψ := by
    filter_upwards [hevU.eventually_nhds, hevL.eventually_nhds, hevD] with σ hσU hσL hσD
    have hσ : 0 < σ.im := hσU.self_of_nhds
    have hL' : w σ ∉ L.lattice := hσL.self_of_nhds
    have hdw : HasDerivAt w (2 * Real.pi * Complex.I * X0.fC σ) σ :=
      (hasDerivAt_eichlerCd_one hσ).add_const c0
    have hdΨ : HasDerivAt Ψ (L.derivWeierstrassP (w σ) * (2 * Real.pi * Complex.I * X0.fC σ) -
        4 * Real.pi * Complex.I * X0.fC σ * X0.yC σ) σ :=
      ((hasDerivAt_wp L hL').comp σ hdw).sub (hD ⟨σ, hσ⟩)
    rw [hdΨ.deriv]
    have hrel := relation_A L hg2 hg3 hL'
    have heq := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation ⟨σ, hσ⟩
    simp only at heq
    simp only [Pi.mul_apply, hh, hΨ]
    field_simp
    linear_combination (2 * X0.fC σ) * (hrel - 4 * heq)
  -- the order argument
  suffices hΨev : ∀ᶠ σ in 𝓝 (τ0 : ℂ), Ψ σ = 0 by
    filter_upwards [hΨev] with σ hσ
    exact sub_eq_zero.mp hσ
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := (hΨa.analyticOrderAt_eq_zero).mp (by rw [← hm]; rfl)
    exact this hΨ0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have h1 : analyticOrderAt (deriv Ψ) (τ0 : ℂ) = n :=
    analyticOrderAt_deriv_of_pos hΨa (by rw [← hm]; rfl)
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hha hΨa, ← hm] at h1
  have : ((n.succ : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← h1]; exact le_add_self
  norm_cast at this
  omega

include hg2 hg3 in
/-- **Global identity (C6).** Under the hypotheses of `local_eq`, for every `σ ∈ ℍ`,
`Φ₁(σ) + c₀ ∉ L` and `℘(Φ₁(σ) + c₀) = x(σ)` (the set where this holds near `σ` is open, closed
in `ℍ` and contains `τ₀`). -/
theorem global_eq (hD : X0.EtaModelDifferential) (τ0 : ℍ) {z0 : ℂ} (hz0 : z0 ∉ L.lattice)
    (hx : L.weierstrassP z0 = X0.xC τ0) (hy : L.derivWeierstrassP z0 = 2 * X0.yC τ0)
    {σ : ℂ} (hσ : 0 < σ.im) :
    eichlerCd 1 σ + (z0 - eichlerCd 1 τ0) ∉ L.lattice ∧
      L.weierstrassP (eichlerCd 1 σ + (z0 - eichlerCd 1 τ0)) = X0.xC σ := by
  set c0 := z0 - eichlerCd 1 τ0 with hc0
  set w : ℂ → ℂ := fun σ => eichlerCd 1 σ + c0 with hw
  have hwτ : w τ0 = z0 := by simp [hw, hc0]
  set P : ℂ → Prop := fun s => w s ∉ L.lattice ∧ L.weierstrassP (w s) = X0.xC s with hP
  set U : Set ℂ := {w : ℂ | 0 < w.im} with hU
  set S : Set ℂ := U ∩ {s | ∀ᶠ t in 𝓝 s, P t} with hS
  have hSo : IsOpen S := U_open.inter isOpen_setOfPred_eventually_nhds
  have hwa : ∀ s ∈ U, AnalyticAt ℂ w s := fun s hs => (analyticAt_eichler hs).add analyticAt_const
  have hwd : ∀ s ∈ U, HasDerivAt w (2 * Real.pi * Complex.I * X0.fC s) s := fun s hs =>
    (hasDerivAt_eichlerCd_one hs).add_const c0
  have hτ0S : (τ0 : ℂ) ∈ S := by
    refine ⟨τ0.im_pos, ?_⟩
    have hevL : ∀ᶠ s in 𝓝 (τ0 : ℂ), w s ∉ L.lattice :=
      (hwa _ τ0.im_pos).continuousAt.eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (hwτ ▸ hz0))
    filter_upwards [hevL, local_eq L hg2 hg3 hD τ0 hz0 hx hy] with s h1 h2
    exact ⟨h1, h2⟩
  have hcl : closure S ∩ U ⊆ S := by
    rintro σ1 ⟨hcl, hσ1⟩
    by_cases hσ1S : σ1 ∈ S
    · exact hσ1S
    have hfreq : ∃ᶠ s in 𝓝[≠] σ1, P s := by
      rw [Filter.frequently_iff]
      intro V hV
      obtain ⟨u, hu, hσu, huV⟩ := mem_nhdsWithin.mp hV
      obtain ⟨s0, hs0u, hs0S⟩ := mem_closure_iff.mp hcl u hu hσu
      have hne : s0 ≠ σ1 := fun h => hσ1S (h ▸ hs0S)
      exact ⟨s0, huV ⟨hs0u, hne⟩, hs0S.2.self_of_nhds⟩
    have hf1 : X0.fC σ1 ≠ 0 := X0.fC_ne_zero ⟨σ1, hσ1⟩
    have hd1 : 2 * Real.pi * Complex.I * X0.fC σ1 ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) hf1
      exact_mod_cast Real.pi_ne_zero
    have hwL : w σ1 ∉ L.lattice := by
      intro hin
      have hwt : Tendsto w (𝓝[≠] σ1) (𝓝[≠] (w σ1)) :=
        tendsto_nhdsWithin_iff.mpr ⟨(hwa σ1 hσ1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          (hwd σ1 hσ1).eventually_ne hd1⟩
      have hc := (tendsto_weierstrassP_cobounded L hin).comp hwt
      rw [← tendsto_norm_atTop_iff_cobounded] at hc
      have hbig := hc.eventually (eventually_gt_atTop (‖X0.xC σ1‖ + 1))
      have hxc : ∀ᶠ s in 𝓝[≠] σ1, ‖X0.xC s‖ < ‖X0.xC σ1‖ + 1 := by
        have := (analyticAt_xC hσ1).continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖X0.xC σ1‖))
        exact this.filter_mono nhdsWithin_le_nhds
      obtain ⟨s, hs, hs1, hs2⟩ := (hfreq.and_eventually (hbig.and hxc)).exists
      simp only [Function.comp] at hs1
      rw [hs.2] at hs1
      linarith
    have hΨa : AnalyticAt ℂ (fun s => L.weierstrassP (w s) - X0.xC s) σ1 :=
      ((L.analyticOnNhd_weierstrassP _ hwL).comp (hwa σ1 hσ1)).sub (analyticAt_xC hσ1)
    have hz : ∀ᶠ s in 𝓝 σ1, L.weierstrassP (w s) - X0.xC s = 0 := by
      rw [← hΨa.frequently_zero_iff_eventually_zero]
      exact hfreq.mono fun s hs => sub_eq_zero.mpr hs.2
    have hevL : ∀ᶠ s in 𝓝 σ1, w s ∉ L.lattice :=
      (hwa σ1 hσ1).continuousAt.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
    refine ⟨hσ1, ?_⟩
    filter_upwards [hevL, hz] with s h1 h2
    exact ⟨h1, sub_eq_zero.mp h2⟩
  have hsub := (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected.subset_of_closure_inter_subset hSo
    ⟨τ0, τ0.im_pos, hτ0S⟩ hcl
  exact (hsub hσ).2.self_of_nhds

include hg2 hg3 in
/-- **The periods of `Φ₁` over `Γ₀(32)` lie in every lattice of `32a1 : y² = x³ + 4x` (C7)**,
given x0-32's differential identity `dx/2y = 2πi f₁ dτ`. -/
theorem period_mem (hD : X0.EtaModelDifferential) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) (τ : ℍ) :
    eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 τ ∈ L.lattice := by
  -- a point `z₀` over `(x(τ), y(τ))`
  obtain ⟨z1, hz1, hx1⟩ := weierstrassP_surjective L (X0.xC τ)
  have hrel := relation_A L hg2 hg3 hz1
  have heqτ := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  obtain ⟨z0, hz0, hx, hy⟩ : ∃ z0, z0 ∉ L.lattice ∧ L.weierstrassP z0 = X0.xC τ ∧
      L.derivWeierstrassP z0 = 2 * X0.yC τ := by
    have hsq : (L.derivWeierstrassP z1 - 2 * X0.yC τ) * (L.derivWeierstrassP z1 + 2 * X0.yC τ) = 0 := by
      rw [hx1] at hrel
      linear_combination hrel - 4 * heqτ
    rcases mul_eq_zero.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, by linear_combination h⟩
    · refine ⟨-z1, fun h' => hz1 (by simpa using neg_mem h'), by rw [L.weierstrassP_neg, hx1], ?_⟩
      rw [L.derivWeierstrassP_neg]; linear_combination -h
  set c0 := z0 - eichlerCd 1 τ with hc0
  set w : ℂ → ℂ := fun σ => eichlerCd 1 σ + c0 with hw
  have hwτ : w τ = z0 := by simp [hw, hc0]
  set ω := eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 τ with hω
  have hG := fun {σ : ℂ} (hσ : 0 < σ.im) => global_eq L hg2 hg3 hD τ hz0 hx hy hσ
  -- `℘(w σ + ω) = ℘(w σ)` on `ℍ`
  have hshift : ∀ σ : ℍ, w σ + ω = w ((γ • σ : ℍ) : ℂ) := by
    intro σ
    have := period_const hγ σ τ
    simp only [hw, hω]
    linear_combination -this
  have hkey : ∀ σ : ℍ, L.weierstrassP (w σ + ω) = L.weierstrassP (w σ) := by
    intro σ
    rw [hshift σ, (hG (γ • σ).im_pos).2, (hG σ.im_pos).2]
    exact ((ZInQ.Contrib.TYZGenus.Shimura.etaModelInvariant γ hγ σ).1)
  -- the identity theorem on `Ω = ℂ ∖ (L ∪ (L − ω))`
  set Ω : Set ℂ := {u | u ∉ L.lattice ∧ u + ω ∉ L.lattice} with hΩ
  have hΩc : IsPreconnected Ω := by
    have hc : ((L.lattice : Set ℂ) ∪ (fun u => u + ω) ⁻¹' (L.lattice : Set ℂ)).Countable :=
      (countable_lattice L).union ((countable_lattice L).preimage (add_left_injective ω))
    have := (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hc).isPreconnected
    convert this using 1
    ext u; simp [hΩ]
  have hsh : ∀ u, u + ω ∉ L.lattice → AnalyticAt ℂ (fun v => L.weierstrassP (v + ω)) u :=
    fun u hu => AnalyticAt.comp (g := L.weierstrassP) (f := fun v => v + ω) (x := u)
      (L.analyticOnNhd_weierstrassP _ hu) (analyticAt_id.add analyticAt_const)
  have hg1a : AnalyticOnNhd ℂ (fun u => L.weierstrassP (u + ω)) Ω := fun u hu => hsh u hu.2
  have hg2a : AnalyticOnNhd ℂ L.weierstrassP Ω := fun u hu => L.analyticOnNhd_weierstrassP _ hu.1
  have hu0 : w τ ∈ Ω := ⟨(hG τ.im_pos).1, by rw [hshift τ]; exact (hG (γ • τ).im_pos).1⟩
  have hwa : AnalyticAt ℂ w τ := (analyticAt_eichler τ.im_pos).add analyticAt_const
  have hwd : HasDerivAt w (2 * Real.pi * Complex.I * X0.fC τ) τ :=
    (hasDerivAt_eichlerCd_one τ.im_pos).add_const c0
  have hd1 : 2 * Real.pi * Complex.I * X0.fC τ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero)
      (X0.fC_ne_zero τ)
    exact_mod_cast Real.pi_ne_zero
  have hmap : 𝓝 (w τ) ≤ Filter.map w (𝓝 (τ : ℂ)) := by
    rcases hwa.eventually_constant_or_nhds_le_map_nhds with h | h
    · exfalso
      have hne := hwd.eventually_ne hd1 (c := w τ)
      obtain ⟨s, hs1, hs2⟩ := ((h.filter_mono nhdsWithin_le_nhds).and hne).exists
      exact hs2 hs1
    · exact h
  have hev : (fun u => L.weierstrassP (u + ω)) =ᶠ[𝓝 (w τ)] L.weierstrassP := by
    refine Filter.Eventually.filter_mono hmap ?_
    rw [Filter.eventually_map]
    filter_upwards [U_open.mem_nhds τ.im_pos] with s hs
    exact hkey ⟨s, hs⟩
  have hEq := hg1a.eqOn_of_preconnected_of_eventuallyEq hg2a hΩc hu0 hev
  -- if `ω ∉ L`, `℘` would be bounded near `0`
  by_contra hωL
  have h0L : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hev0 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ Ω := by
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∉ L.lattice := by
      filter_upwards [nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ))
        (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with u hu hu0
      exact fun huL => hu ⟨huL, hu0⟩
    have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), u + ω ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ => u + ω) 0 := (continuous_id.add continuous_const).continuousAt
      exact hc.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hωL))
    filter_upwards [h1, h2.filter_mono nhdsWithin_le_nhds] with u hu1 hu2
    exact ⟨hu1, hu2⟩
  have hcont : ContinuousAt (fun u => L.weierstrassP (u + ω)) 0 :=
    (hsh 0 (by simpa using hωL)).continuousAt
  have hb : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖L.weierstrassP (u + ω)‖ < ‖L.weierstrassP ω‖ + 1 := by
    have h0 : (fun u => ‖L.weierstrassP (u + ω)‖) 0 < ‖L.weierstrassP ω‖ + 1 := by simp
    exact (hcont.norm.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
  have hc := tendsto_weierstrassP_cobounded L h0L
  rw [← tendsto_norm_atTop_iff_cobounded] at hc
  have hbig := hc.eventually (eventually_gt_atTop (‖L.weierstrassP ω‖ + 1))
  obtain ⟨u, hu1, hu2, hu3⟩ := (hev0.and (hb.and hbig)).exists
  have he := hEq hu1
  simp only at he
  rw [he] at hu2
  linarith

end Param

/-! ## C8. The two-lattice trick -/

/-- **`ModularParamC1` from x0-32's differential identity** (`X0.EtaModelDifferential`:
`dx/2y = 2πi f₁ dτ` on the eta-quotient model `y² = x³ + 4x` of `X₀(32)`), with `c = 2`: the
lattices `((1 ± i)/2) L` of `32a1` both contain the periods of `Φ₁` (`period_mem`). -/
theorem modularParamC1_of_etaModelDifferential (hD : ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential) :
    ModularParamC1 := by
  intro L hL
  obtain ⟨h2, h3⟩ := (isPeriodLattice_cd_iff 1 L).mp hL
  have hl1 : (1 + Complex.I) / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hl2 : (1 - Complex.I) / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hp1 : ((1 + Complex.I) / 2) ^ 4 = -1 / 4 := by
    ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
      Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring
  have hp2 : ((1 - Complex.I) / 2) ^ 4 = -1 / 4 := by
    ring_nf; rw [show Complex.I ^ 4 = 1 by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]; simp,
      Complex.I_sq, show Complex.I ^ 3 = -Complex.I by rw [pow_succ, Complex.I_sq]; ring]; ring
  have hL1 : (scalePP L _ hl1).g₂ = -16 := by rw [g₂_scalePP, h2, hp1]; push_cast; norm_num
  have hL1' : (scalePP L _ hl1).g₃ = 0 := by rw [g₃_scalePP, h3, mul_zero]
  have hL2 : (scalePP L _ hl2).g₂ = -16 := by rw [g₂_scalePP, h2, hp2]; push_cast; norm_num
  have hL2' : (scalePP L _ hl2).g₃ = 0 := by rw [g₃_scalePP, h3, mul_zero]
  refine ⟨2, two_ne_zero, fun γ hγ τ => ?_⟩
  obtain ⟨a, ha, hωa⟩ := (mem_scalePP hl1).mp (period_mem _ hL1 hL1' hD hγ τ)
  obtain ⟨b, hb, hωb⟩ := (mem_scalePP hl2).mp (period_mem _ hL2 hL2' hD hγ τ)
  have : ((2 : ℚ) : ℂ) * (eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) = a + b := by
    have e : ((2 : ℚ) : ℂ) * (eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) =
        (1 - Complex.I) * (eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) +
          (1 + Complex.I) * (eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) := by
      push_cast; ring
    rw [e]
    nth_rewrite 1 [hωa]
    rw [hωb]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (a / 2 + b / 2) * (-hI)
  rw [this]
  exact add_mem ha hb

end ZInQ.GZWeil

namespace ZInQ.GZWeil

/-- **gz-hl3's `ShimuraCMParamCd` from x0-32's eta-quotient identity alone** (no
`StrongWeilCurve`, no `IsogenyLattice`). -/
theorem shimuraCMParamCd_of_etaModelDifferential
    (hD : ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential) : ZInQ.GZHL3.ShimuraCMParamCd :=
  shimuraCMParamCd_of_modularParamC1 (modularParamC1_of_etaModelDifferential hD)

/-- **`GZStatements.GrossZagierHeegnerCd` (`hL3` restricted to the curves of the proof) from
uniformization, x0-32's eta-quotient identity and gz-hl3's three Heegner-point leaves for `C_d`.** -/
theorem grossZagierHeegnerCd_of_weil (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hD : ZInQ.Contrib.TYZGenus.X0.EtaModelDifferential) (hHP : ZInQ.GZHL3.HeegnerPointRationalCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  ZInQ.GZHL3.grossZagierHeegnerCd_of_leaves hU (shimuraCMParamCd_of_etaModelDifferential hD) hHP
    hGZ hGC

end ZInQ.GZWeil
