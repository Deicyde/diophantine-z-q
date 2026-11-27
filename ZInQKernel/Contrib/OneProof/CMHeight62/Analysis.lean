import Mathlib

/-! # cmheight62-p1, step 4 (third bullet, analytic half): `−2℘/℘'` at `0`

`℘(w) = 1/w² + g(w)` and `℘'(w) = −2/w³ + h(w)` with `g, h` analytic at `0` (Mathlib's
`℘[L - 0]`, `℘'[L - 0]`). Hence `−2℘(w)/(u℘'(w)) = ψ(w)` near `0` (`w ≠ 0`), with
`ψ(w) = −2(w + w³g(w)) / (u(−2 + w³h(w)))` analytic at `0`, `ψ(0) = 0`, `ψ'(0) = 1/u`
(this is `z²℘(z) → 1`, `z³℘'(z) → −2`). A function continuous at `0` that agrees with
`w ↦ ψ(a w)` on a punctured neighbourhood has derivative `a/u` at `0`. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open Filter Topology

variable (L : PeriodPair)

/-- `g = ℘ − 1/w²` near `0`. -/
def wpReg : ℂ → ℂ := L.weierstrassPExcept 0

/-- `h = ℘' + 2/w³` near `0`. -/
def dwpReg : ℂ → ℂ := L.derivWeierstrassPExcept 0

theorem wp_eq (w : ℂ) : L.weierstrassP w = 1 / w ^ 2 + wpReg L w := by
  have h := L.weierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ w
  rw [wpReg, h]
  simp

theorem dwp_eq (w : ℂ) : L.derivWeierstrassP w = -2 / w ^ 3 + dwpReg L w := by
  have h := L.derivWeierstrassPExcept_def ⟨0, L.lattice.zero_mem⟩ w
  rw [dwpReg, h]
  simp [neg_div]

theorem analyticAt_wpReg : AnalyticAt ℂ (wpReg L) 0 := L.analyticAt_weierstrassPExcept 0
theorem analyticAt_dwpReg : AnalyticAt ℂ (dwpReg L) 0 := L.analyticAt_derivWeierstrassPExcept 0

/-- The numerator `N(w) = −2(w + w³ g(w))`. -/
def numψ (w : ℂ) : ℂ := -2 * (w + w ^ 3 * wpReg L w)
/-- The denominator `−2 + w³ h(w)`. -/
def denψ (w : ℂ) : ℂ := -2 + w ^ 3 * dwpReg L w

theorem hasDerivAt_pow3 : HasDerivAt (fun w : ℂ => w ^ 3) 0 0 := by
  simpa using hasDerivAt_pow 3 (0 : ℂ)

theorem hasDerivAt_numψ : HasDerivAt (numψ L) (-2) 0 := by
  have hg := (analyticAt_wpReg L).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_id' (0 : ℂ)).add ((hasDerivAt_pow3).mul hg)).const_mul (-2 : ℂ)
  unfold numψ
  convert h using 1
  simp

theorem hasDerivAt_denψ : HasDerivAt (denψ L) 0 0 := by
  have hh := (analyticAt_dwpReg L).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_pow3).mul hh).const_add (-2 : ℂ)
  unfold denψ
  convert h using 1
  simp

theorem numψ_zero : numψ L 0 = 0 := by simp [numψ]
theorem denψ_zero : denψ L 0 = -2 := by simp [denψ]

/-- `ψ = N / (u · den)`. -/
def ψ (u : ℂ) (w : ℂ) : ℂ := numψ L w / (u * denψ L w)

theorem hasDerivAt_ψ {u : ℂ} (hu : u ≠ 0) : HasDerivAt (ψ L u) (1 / u) 0 := by
  have hd : u * denψ L 0 ≠ 0 := by rw [denψ_zero]; simpa using hu
  have h := (hasDerivAt_numψ L).div ((hasDerivAt_denψ L).const_mul u) hd
  unfold ψ
  convert h using 1
  rw [numψ_zero, denψ_zero]
  field_simp
  ring

theorem ψ_zero (u : ℂ) : ψ L u 0 = 0 := by simp [ψ, numψ_zero]

theorem dwp_eq_den {w : ℂ} (hw : w ≠ 0) :
    L.derivWeierstrassP w = denψ L w / w ^ 3 := by
  rw [dwp_eq, denψ]
  field_simp

/-- `−2℘(w)/(u℘'(w)) = ψ(w)` for `w ≠ 0` with `den(w) ≠ 0`. -/
theorem ratio_eq_ψ (u : ℂ) {w : ℂ} (hw : w ≠ 0) (hd : denψ L w ≠ 0) :
    -2 * L.weierstrassP w / (u * L.derivWeierstrassP w) = ψ L u w := by
  rw [dwp_eq_den L hw, wp_eq, ψ, numψ]
  have hw3 : w ^ 3 ≠ 0 := pow_ne_zero 3 hw
  by_cases hu : u = 0
  · simp [hu]
  field_simp

theorem eventually_denψ_ne_zero : ∀ᶠ w in 𝓝 (0 : ℂ), denψ L w ≠ 0 := by
  have hc : ContinuousAt (denψ L) 0 :=
    ((hasDerivAt_denψ L).differentiableAt).continuousAt
  exact hc.eventually_ne (y := 0) (by rw [denψ_zero]; norm_num)

/-- `℘'(w) ≠ 0` when `den(w) ≠ 0`, `w ≠ 0`. -/
theorem dwp_ne_zero {w : ℂ} (hw : w ≠ 0) (hd : denψ L w ≠ 0) : L.derivWeierstrassP w ≠ 0 := by
  rw [dwp_eq_den L hw]
  exact div_ne_zero hd (pow_ne_zero 3 hw)

/-- **The derivative.** If `f` is continuous at `0` and `f(w) = ψ(a w)` on a punctured
neighbourhood of `0`, then `f'(0) = a/u`. -/
theorem hasDerivAt_of_eventually_ψ {u a : ℂ} (hu : u ≠ 0) {f : ℂ → ℂ}
    (hf : ContinuousAt f 0) (heq : ∀ᶠ w in 𝓝[≠] (0 : ℂ), f w = ψ L u (a * w)) :
    HasDerivAt f (a / u) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => a * w) a 0 := by
    simpa using (hasDerivAt_id' (0 : ℂ)).const_mul a
  have h2 : HasDerivAt (ψ L u) (1 / u) (a * 0) := by rw [mul_zero]; exact hasDerivAt_ψ L hu
  have hψa : HasDerivAt (fun w => ψ L u (a * w)) (1 / u * a) 0 := h2.comp (0 : ℂ) h1
  have hlim1 : Tendsto f (𝓝[≠] 0) (𝓝 (f 0)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun w => ψ L u (a * w)) (𝓝[≠] 0) (𝓝 (ψ L u (a * 0))) :=
    hψa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hf0 : f 0 = ψ L u (a * 0) :=
    tendsto_nhds_unique hlim1 (hlim2.congr' (heq.mono fun w h => h.symm))
  have heq' : f =ᶠ[𝓝 0] fun w => ψ L u (a * w) := by
    rw [← nhdsNE_sup_pure]
    exact Filter.eventually_sup.mpr ⟨heq, Filter.eventually_pure.mpr hf0⟩
  have := hψa.congr_of_eventuallyEq heq'
  convert this using 1
  field_simp

end ZInQ.Contrib.CMHeight62
