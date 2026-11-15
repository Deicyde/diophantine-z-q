import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam

/-!
# gz-weil: x0-32's eta-quotient identity from Jacobi's derivative formula for `λ`

Task gz-weil (2026-11-15). Report: `docs/research/gz-weil.md`; scratch and log: `scratch/gz-weil/`.

`X0.EtaModelDifferential` (`x'(τ) = 4πi f₁(τ) y(τ)` on the eta-quotient model of `X₀(32)`, the only
input of `WeilParam.lean` not proved in the kernel) is proved here from one classical printed
identity, Jacobi's derivative formula for the modular function `λ = θ₂⁴/θ₃⁴`:
`dλ/dt = πi λ θ₄⁴` (`JacobiLambdaDeriv`, stated over Mathlib's `jacobiTheta₂`; proved in
`WeilJacobi.lean`). The glue:

* `x = 2θ₃(16τ)/θ₂(16τ)`, `y = −θ₂(4τ)²/θ₂(16τ)²` (tyz-cm's `xC_theta`, `yC_theta`);
* `x' = −4πi x θ₄(16τ)⁴` from the leaf (chain rule, `θ₂, θ₃ ≠ 0` from the triple product);
* the product identity `f₁ θ₂(4τ)² = 2θ₂θ₃θ₄⁴(16τ)` (`product_star`; gz-theta's triple product,
  tyz-cm's product forms and Euler's identity), which turns `−x θ₄(16τ)⁴` into `f₁ y`.

Main results: `etaModelDifferential_of_jacobiLambdaDeriv`, `shimuraCMParamCd_of_jacobiLambdaDeriv`,
`grossZagierHeegnerCd_of_printed`. The formula itself is proved in `WeilJacobi.lean`.
No `sorry`, no `axiom`.
-/

noncomputable section

open Complex Filter Topology
open scoped Real

namespace ZInQ.GZWeil

open ZInQ.Contrib.TYZGenus ZInQ.Contrib.TYZGenus.Shimura
open ZInQ.GZTheta (gp gp_even_mul_odd gp_pow jtpA_eq_gp jtpB_eq_gp jtpP qJ eJ jacobiTheta₂_eq_jtpP)

/-! ## The theta constants and Jacobi's derivative formula -/

/-- `θ₂(t) = Σ_{n ∈ ℤ} e^{πi(n + 1/2)² t}`. -/
def thetaTwo (t : ℂ) : ℂ := cexp (π * I * t / 4) * jacobiTheta₂ (t / 2) t

/-- `θ₃(t) = Σ_{n ∈ ℤ} e^{πin² t}`. -/
def thetaThree (t : ℂ) : ℂ := jacobiTheta₂ 0 t

/-- `θ₄(t) = Σ_{n ∈ ℤ} (−1)ⁿ e^{πin² t}`. -/
def thetaFour (t : ℂ) : ℂ := jacobiTheta₂ (1 / 2) t

/-- **Jacobi's derivative formula for the modular function `λ`** (proved in `WeilJacobi.lean`:
`jacobiLambdaDeriv`; stated here as a `Prop` so that the reduction below is independent). With
`θ₂(t) = Σ e^{πi(n+1/2)²t}`, `θ₃(t) = Σ e^{πin²t}`, `θ₄(t) = Σ (−1)ⁿ e^{πin²t}` (`Im t > 0`) and
`λ = θ₂⁴/θ₃⁴`: `dλ/dt = πi λ θ₄⁴`; equivalently `d/dt log(θ₂/θ₃) = (πi/4) θ₄⁴`.

Classical (Jacobi, *Fundamenta nova*, 1829). Printed e.g. in K. Chandrasekharan, *Elliptic
functions*, Grundlehren 281 (1985), Ch. VII; R. A. Rankin, *Modular forms and functions* (1977),
§7.?; D. F. Lawden, *Elliptic functions and applications* (1989), §3.? (all locators UNVERIFIED:
no copy on this host). VERIFIED numerically here at three points to 10⁻⁹
(`scratch/gz-weil/lambda_check.py`). -/
def JacobiLambdaDeriv : Prop :=
  ∀ t : ℂ, 0 < t.im → HasDerivAt (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4)
    (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t

/-! ## Product forms at `16τ` -/

theorem theta_half_sixteen {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (1 / 2) (16 * τ) = gp (Qt τ) (-1) 16 16 * gp (Qt τ) (-1) 16 8 ^ 2 := by
  have h16 : 0 < (16 * τ).im := by simp; linarith
  rw [jacobiTheta₂_eq_jtpP h16]
  unfold jtpP
  rw [jtpA_eq_gp, jtpB_eq_gp, jtpB_eq_gp, ZInQ.GZTheta.eJ_neg_half,
    show (16 : ℂ) * τ = ((2 * 8 : ℕ) : ℂ) * τ by norm_num, qJ_mul_nat,
    ZInQ.GZTheta.eJ_half, gp_pow, gp_pow]
  norm_num
  ring

/-- **The product identity** `f₁(τ) θ(2τ; 4τ)² = 2 Q θ(0; 16τ) θ(8τ; 16τ) θ(1/2; 16τ)⁴`,
`Q = e^{2πiτ}`, `f₁ = η(4τ)²η(8τ)²` (equivalently `f₁ θ₂(4τ)² = 2 θ₂θ₃θ₄⁴(16τ)`). -/
theorem product_star (τ : UpperHalfPlane) :
    X0.fC τ * jacobiTheta₂ (2 * τ) (4 * τ) ^ 2 =
      2 * Qt τ * jacobiTheta₂ 0 (16 * τ) * jacobiTheta₂ (8 * τ) (16 * τ) *
        jacobiTheta₂ (1 / 2) (16 * τ) ^ 4 := by
  have hτ := τ.im_pos
  have hq := norm_Qt_lt_one hτ
  have hG8 : gp (Qt τ) (-1) 8 8 = gp (Qt τ) (-1) 16 8 * gp (Qt τ) (-1) 16 16 := by
    have := gp_even_mul_odd hq (-1) 8 8 (by norm_num); norm_num at this; rw [← this]
  have hGG : gp (Qt τ) (-1) 4 4 * gp (Qt τ) 1 4 4 = gp (Qt τ) (-1) 8 8 := by
    have := gp_mul_neg hq 4 4 (by norm_num); norm_num at this; exact this
  have heul := euler_BCD hτ
  rw [theta_two_four hτ, theta00_sixteen hτ, theta_eight_sixteen hτ, theta_half_sixteen hτ]
  unfold X0.fC
  simp only [X0.etaD]
  rw [eta_eq_gp 4, eta_eq_gp 8]
  have h24 : X0.wz (τ : ℂ) ^ 24 = Qt τ := by rw [X0.wz_pow_24, Qt_def]
  set w := X0.wz (τ : ℂ)
  set A := gp (Qt τ) (-1) 16 16
  set B := gp (Qt τ) 1 16 16
  set C := gp (Qt τ) 1 16 8
  set D := gp (Qt τ) (-1) 16 8
  set G4 := gp (Qt τ) (-1) 4 4
  set H4 := gp (Qt τ) 1 4 4
  set G8 := gp (Qt τ) (-1) 8 8
  have hfac : (w ^ 4 * G4) ^ 2 * (w ^ 8 * G8) ^ 2 * (2 * G4 * H4 ^ 2) ^ 2 =
      4 * w ^ 24 * (G4 * H4) ^ 4 * G8 ^ 2 := by ring
  rw [hfac, hGG, h24, hG8]
  linear_combination (4 * Qt τ * A ^ 6 * D ^ 6 * (1 + B * C * D)) * (-heul)

/-! ## `X0.EtaModelDifferential` from Jacobi's derivative formula -/

theorem thetaTwo_sixteen (σ : ℂ) :
    thetaTwo (16 * σ) = Qt σ ^ 2 * jacobiTheta₂ (8 * σ) (16 * σ) := by
  rw [thetaTwo, Qt_def, ← Complex.exp_nat_mul]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; ring

theorem differentiableAt_thetaTwo {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ thetaTwo t := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (s / 2, s)) t :=
    (differentiableAt_id.div_const 2).prodMk differentiableAt_id
  have h2 := (hasFDerivAt_jacobiTheta₂ (t / 2) ht).differentiableAt
  have h3 : DifferentiableAt ℂ (fun s => jacobiTheta₂ (s / 2) s) t :=
    DifferentiableAt.comp (f := fun s : ℂ => (s / 2, s))
      (g := fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) t h2 h1
  have h4 : DifferentiableAt ℂ (fun s : ℂ => cexp (π * I * s / 4)) t :=
    ((differentiableAt_id.const_mul (π * I : ℂ)).div_const 4).cexp
  exact h4.mul h3

theorem differentiableAt_thetaThree {t : ℂ} (ht : 0 < t.im) : DifferentiableAt ℂ thetaThree t :=
  differentiableAt_jacobiTheta₂_snd 0 ht

/-- **x0-32's `X0.EtaModelDifferential` (`x' = 4πi f₁ y`) from Jacobi's derivative formula**:
`x = 2θ₃(16τ)/θ₂(16τ)` and `y = −θ₂(4τ)²/θ₂(16τ)²` (tyz-cm's theta forms), so
`x' = −4πi x θ₄(16τ)⁴` by `λ' = πiλθ₄⁴`, and `−x θ₄(16τ)⁴ = f₁ y` is the product identity
`product_star`. -/
theorem etaModelDifferential_of_jacobiLambdaDeriv (h : JacobiLambdaDeriv) :
    X0.EtaModelDifferential := by
  intro τ
  set z : ℂ := (τ : ℂ) with hz
  have hτ : 0 < z.im := τ.im_pos
  have h16 : ∀ σ : ℂ, 0 < σ.im → 0 < (16 * σ).im := fun σ hσ => by simp; linarith
  set R : ℂ → ℂ := fun σ => thetaThree (16 * σ) / thetaTwo (16 * σ) with hR
  -- `x = 2R` on `ℍ`
  have hxR : X0.xC =ᶠ[𝓝 z] fun σ => 2 * R σ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ] with σ hσ
    have := xC_theta ⟨σ, hσ⟩
    show X0.xC σ = 2 * (thetaThree (16 * σ) / thetaTwo (16 * σ))
    rw [this, thetaTwo_sixteen, thetaThree]
    ring
  -- nonvanishing
  have hA := gp_A_ne_zero hτ 8 (by norm_num)
  norm_num at hA
  have heul := euler_BCD hτ
  have hB : gp (Qt z) 1 16 16 ≠ 0 := fun h0 => by rw [h0] at heul; simp at heul
  have hC : gp (Qt z) 1 16 8 ≠ 0 := fun h0 => by rw [h0] at heul; simp at heul
  have hT0 : thetaThree (16 * z) ≠ 0 := by
    rw [thetaThree, theta00_sixteen hτ]; exact mul_ne_zero hA (pow_ne_zero _ hC)
  have hT1 : jacobiTheta₂ (8 * z) (16 * z) ≠ 0 := by
    rw [theta_eight_sixteen hτ]; exact mul_ne_zero (mul_ne_zero two_ne_zero hA) (pow_ne_zero _ hB)
  have hQ := Qt_ne_zero z
  have hT2 : thetaTwo (16 * z) ≠ 0 := by
    rw [thetaTwo_sixteen]; exact mul_ne_zero (pow_ne_zero _ hQ) hT1
  -- `R` is differentiable at `z`
  have hd16 : HasDerivAt (fun σ : ℂ => 16 * σ) 16 z := by
    simpa using (hasDerivAt_id z).const_mul (16 : ℂ)
  have hRd : DifferentiableAt ℂ R z := by
    have a := (differentiableAt_thetaThree (h16 z hτ)).comp z hd16.differentiableAt
    have b := (differentiableAt_thetaTwo (h16 z hτ)).comp z hd16.differentiableAt
    exact a.div b hT2
  set D := deriv R z with hDdef
  have hRD : HasDerivAt R D z := hRd.hasDerivAt
  have hRz : R z ≠ 0 := div_ne_zero hT0 hT2
  -- the leaf at `16 z`
  have hS := (h (16 * z) (h16 z hτ)).comp z hd16
  have hSR : ((fun s => thetaTwo s ^ 4 / thetaThree s ^ 4) ∘ fun σ : ℂ => 16 * σ) =
      fun σ => (R σ ^ 4)⁻¹ := by
    funext σ; simp only [Function.comp, hR, div_pow, inv_div]
  rw [hSR] at hS
  have hS' := (hRD.pow 4).inv (pow_ne_zero 4 hRz)
  have huniq := hS.unique hS'
  -- solve for `D`
  have hDval : D = -(4 * π * I) * R z * thetaFour (16 * z) ^ 4 := by
    have e1 : thetaTwo (16 * z) ^ 4 / thetaThree (16 * z) ^ 4 = (R z ^ 4)⁻¹ := by
      simp only [hR, div_pow, inv_div]
    rw [e1] at huniq
    simp only [Pi.pow_apply] at huniq
    generalize R z = r at huniq hRz ⊢
    have h4 : r ^ 4 ≠ 0 := pow_ne_zero 4 hRz
    field_simp at huniq
    norm_num at huniq
    apply mul_left_cancel₀ (pow_ne_zero 3 hRz)
    linear_combination (1 / 4 : ℂ) * huniq
  -- conclude
  have hx' : HasDerivAt X0.xC (2 * D) z :=
    (hRD.const_mul 2).congr_of_eventuallyEq hxR
  convert hx' using 1
  rw [hDval]
  have hstar := product_star τ
  have hy := yC_theta τ
  rw [← hz] at hstar hy
  rw [hy]
  simp only [hR, thetaTwo_sixteen, thetaThree, thetaFour]
  have hT0' : jacobiTheta₂ 0 (16 * z) ≠ 0 := hT0
  generalize X0.fC z = a at hstar ⊢
  generalize jacobiTheta₂ (2 * z) (4 * z) = b at hstar ⊢
  generalize jacobiTheta₂ (8 * z) (16 * z) = c at hstar hT1 ⊢
  generalize jacobiTheta₂ 0 (16 * z) = d at hstar hT0' ⊢
  generalize jacobiTheta₂ (1 / 2) (16 * z) = e at hstar ⊢
  generalize Qt z = q at hstar hQ ⊢
  field_simp
  linear_combination (-1 : ℂ) * hstar


/-! ## Consequences -/

/-- `ModularParamC1` from Jacobi's derivative formula. -/
theorem modularParamC1_of_jacobiLambdaDeriv (h : JacobiLambdaDeriv) : ModularParamC1 :=
  modularParamC1_of_etaModelDifferential (etaModelDifferential_of_jacobiLambdaDeriv h)

/-- **gz-hl3's `ShimuraCMParamCd` (the analytic modular parametrization of every `C_d`) from
Jacobi's derivative formula alone.** -/
theorem shimuraCMParamCd_of_jacobiLambdaDeriv (h : JacobiLambdaDeriv) :
    ZInQ.GZHL3.ShimuraCMParamCd :=
  shimuraCMParamCd_of_etaModelDifferential (etaModelDifferential_of_jacobiLambdaDeriv h)

/-- **`GZStatements.GrossZagierHeegnerCd` (`hL3` for the curves of the proof) from printed leaves
and gz-hl3's Heegner-point leaf**: uniformization, Jacobi's derivative formula,
`HeegnerPointRationalCd`, the Gross–Zagier formula and Gross's conjugation relation. -/
theorem grossZagierHeegnerCd_of_printed (hU : ZInQ.GZHL3.WeierstrassUniformization)
    (hJ : JacobiLambdaDeriv) (hHP : ZInQ.GZHL3.HeegnerPointRationalCd)
    (hGZ : ZInQ.GZHL3.GrossZagierFormulaCd) (hGC : ZInQ.GZHL3.GrossConjugationCd) :
    ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_weil hU (etaModelDifferential_of_jacobiLambdaDeriv hJ) hHP hGZ hGC

end ZInQ.GZWeil
