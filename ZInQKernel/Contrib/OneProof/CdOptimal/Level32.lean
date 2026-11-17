import ZInQKernel.Contrib.OneProof.CdOptimal.Structure
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilJacobi

/-!
# cd-optimal: the periods of `Φ₁` over `Γ₀(32) ∩ {d ≡ ±1 mod 8}` lie in every lattice of `C₁`

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; log: `scratch/cd-optimal/log.md`.

On x0-32's eta model `y² = x³ + 4x` of `X₀(32) = 32a1`, `w = η(16τ)³/(η(8τ)η(32τ)²)` satisfies
`w² = x` (tyz-cm's `xC_eq_even`), so `s = −y/w` satisfies `s² = x² + 4` and `x₁ = (x + s)/2`,
`y₁ = y x₁²/(1 + x₁²)` satisfy `y₁² = x₁³ − x₁` (`C₁ = 32a2`) and `dx₁/2y₁ = dx/2y = 2πi f₁ dτ`
(`x₁ ↦ x₁ − 1/x₁` is the 2-isogeny `C₁ → 32a1`). `w` has the character `(2/d)` on `Γ₀(32)` (the
eta-quotient transformation law for `v = 1/w`; printed leaf `EtaW32Character`), so `x₁, y₁` are invariant under
the `γ ∈ Γ₀(32)` with `(2/d) = 1`, and gz-weil's argument (`Unif.lean`, `period_mem_gen`) puts the
periods of `Φ₁` over those `γ` into every lattice `L₁` of `C₁` (`period_mem_C1`).

Then the twist (`LamCd_le_of_etaW32`): for `γ ∈ Γ₀(32 d²)`, `g (Φ_d(γτ) − Φ_d(τ)) =
Σ_a χ_d(a) ρ(γ'_a)` with all `γ'_a` sharing `d ≡ D (mod 32)`; `ρ(γ'_a) − ρ(γ'_0) ∈ L₁` and
`Σ_a χ_d(a) = 0`, so `Λ_d ⊆ g⁻¹ L₁ = L` for every lattice `L` of `C_d`. No `sorry`, no `axiom`.
-/

noncomputable section

open Complex CongruenceSubgroup Filter Topology
open scoped UpperHalfPlane MatrixGroups ComplexConjugate ZMod
open ZInQ.Contrib.TYZGenus
open ZInQ.GZWeil (eichlerCd moeb)
open Matrix.GeneralLinearGroup (upperRightHom)
open Matrix.SpecialLinearGroup (mapGL)

namespace ZInQ.CdOpt

/-! ## §1. The eta quotient `w` and the printed leaf -/

/-- `w(τ) = η(16τ)³ / (η(8τ) η(32τ)²)`. -/
def wC (z : ℂ) : ℂ := X0.etaD 16 z ^ 3 / (X0.etaD 8 z * X0.etaD 32 z ^ 2)

/-- `v(τ) = 1/w(τ) = η(8τ) η(32τ)² / η(16τ)³`. -/
def vC (z : ℂ) : ℂ := X0.etaD 8 z * X0.etaD 32 z ^ 2 / X0.etaD 16 z ^ 3

theorem wC_eq_inv (z : ℂ) : wC z = (vC z)⁻¹ := by
  rw [wC, vC, inv_div]

/-- **The transformation law of the eta quotient `v = η(8τ)η(32τ)²/η(16τ)³` on `Γ₀(32)`**
(printed leaf; Newman, Gordon–Hughes): `v(γτ) = (2/d) v(τ)` for `γ = [a, b; c, d] ∈ Γ₀(32)`.

The theorem of Newman (1957, 1959) and Gordon–Hughes (1981), as stated in K. Ono, *The web of
modularity* (CBMS 102, 2004), Thm 1.64 (UNVERIFIED locator): if `f = ∏_{δ ∣ N} η(δτ)^{r_δ}` with
`k = ½ Σ r_δ ∈ ℤ`, `Σ δ r_δ ≡ 0 (mod 24)` and `Σ (N/δ) r_δ ≡ 0 (mod 24)`, then
`f(γτ) = χ(d) (cτ + d)^k f(τ)` for every `γ ∈ Γ₀(N)`, with `χ(d) = ((−1)^k s / d)`,
`s = ∏ δ^{r_δ}`. Here `N = 32`, `r₈ = 1`, `r₁₆ = −3`, `r₃₂ = 2`: `k = 0`, `Σ δ r_δ = 24`,
`Σ (32/δ) r_δ = 0`, `s = 8 · 32² / 16³ = 2`, so `χ(d) = (2/d)`. Stated with Mathlib's `χ₈ = (2/·)`
on `ℤ/8` (the Kronecker symbol `(2/d)` for odd `d`, even in `d`, so `−γ` and `γ` agree). A
consequence of the print (one instance). Checked numerically for 602 matrices
(`scratch/cd-optimal/py/wchar.gp`, for `w = 1/v`). -/
def EtaW32Character : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 32 → ∀ τ : ℍ,
    vC ((γ • τ : ℍ) : ℂ) = ((ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) : ℤ) : ℂ) * vC τ

theorem wC_ne_zero (τ : ℍ) : wC τ ≠ 0 := by
  unfold wC
  have := X0.etaD_ne_zero (d := 8) (by norm_num) τ
  have := X0.etaD_ne_zero (d := 16) (by norm_num) τ
  have := X0.etaD_ne_zero (d := 32) (by norm_num) τ
  positivity

theorem wC_sq (τ : ℍ) : wC τ ^ 2 = X0.xC τ := by
  rw [ZInQ.Contrib.TYZGenus.Shimura.xC_eq_even τ, wC]
  ring

theorem differentiableAt_wC (τ : ℍ) : DifferentiableAt ℂ wC τ := by
  unfold wC
  refine DifferentiableAt.div ?_ ?_ ?_
  · exact (X0.differentiableAt_etaD (by norm_num) τ).pow 3
  · exact (X0.differentiableAt_etaD (by norm_num) τ).mul
      ((X0.differentiableAt_etaD (by norm_num) τ).pow 2)
  · exact mul_ne_zero (X0.etaD_ne_zero (by norm_num) τ)
      (pow_ne_zero 2 (X0.etaD_ne_zero (by norm_num) τ))

/-! ## §2. The model `x₁, y₁` of `C₁ : y² = x³ − x` -/

/-- `s = −y/w`, `s² = x² + 4`. -/
def sC (z : ℂ) : ℂ := -X0.yC z / wC z

/-- `x₁ = (x + s)/2`, a root of `X² − x X − 1`. -/
def x1C (z : ℂ) : ℂ := (X0.xC z + sC z) / 2

/-- `y₁ = y x₁² / (1 + x₁²)`. -/
def y1C (z : ℂ) : ℂ := X0.yC z * x1C z ^ 2 / (1 + x1C z ^ 2)

theorem xC_ne_zero (τ : ℍ) : X0.xC τ ≠ 0 := by
  rw [← wC_sq]; exact pow_ne_zero 2 (wC_ne_zero τ)

theorem sC_sq (τ : ℍ) : sC τ ^ 2 = X0.xC τ ^ 2 + 4 := by
  have hw := wC_ne_zero τ
  have hx := xC_ne_zero τ
  have he := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  have hw2 := wC_sq τ
  unfold sC
  rw [div_pow, neg_sq, he, hw2]
  field_simp

theorem x1_quad (τ : ℍ) : x1C τ ^ 2 - X0.xC τ * x1C τ - 1 = 0 := by
  have h := sC_sq τ
  unfold x1C
  linear_combination h / 4

theorem x1_ne_zero (τ : ℍ) : x1C τ ≠ 0 := by
  intro h; have := x1_quad τ; rw [h] at this; norm_num at this

theorem one_add_x1_sq_ne_zero (τ : ℍ) : 1 + x1C τ ^ 2 ≠ 0 := by
  intro h
  have hq := x1_quad τ
  have hx1 := x1_ne_zero τ
  -- then `x = 2 x₁` and `s = 0`, so `y = 0`
  have hx : X0.xC τ = 2 * x1C τ := by
    have : x1C τ * (X0.xC τ - 2 * x1C τ) = 0 := by linear_combination -hq - h
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hx1
    · linear_combination h1
  have hs : sC τ = 0 := by
    have : sC τ = 2 * x1C τ - X0.xC τ := by unfold x1C; ring
    rw [this, hx]; ring
  have hy := X0.yC_ne_zero τ
  apply hy
  have hw := wC_ne_zero τ
  unfold sC at hs
  rw [div_eq_zero_iff] at hs
  rcases hs with h1 | h1
  · exact neg_eq_zero.mp h1
  · exact absurd h1 hw

theorem y1_sq (τ : ℍ) : y1C τ ^ 2 = x1C τ ^ 3 - x1C τ := by
  have hq := x1_quad τ
  have he := ZInQ.Contrib.TYZGenus.Shimura.etaModelEquation τ
  have hd := one_add_x1_sq_ne_zero τ
  have hx1 := x1_ne_zero τ
  -- `x = (x₁² − 1)/x₁`
  have hx : X0.xC τ * x1C τ = x1C τ ^ 2 - 1 := by linear_combination -hq
  unfold y1C
  rw [div_pow, mul_pow, he]
  rw [div_eq_iff (pow_ne_zero 2 hd)]
  have : (X0.xC τ ^ 3 + 4 * X0.xC τ) * x1C τ ^ 3 = (x1C τ ^ 2 - 1) * (1 + x1C τ ^ 2) ^ 2 := by
    have e : (X0.xC τ * x1C τ) ^ 3 + 4 * (X0.xC τ * x1C τ) * x1C τ ^ 2 =
        (x1C τ ^ 2 - 1) * (1 + x1C τ ^ 2) ^ 2 := by rw [hx]; ring
    linear_combination e
  linear_combination x1C τ * this

theorem y1_ne_zero (τ : ℍ) : y1C τ ≠ 0 := by
  unfold y1C
  exact div_ne_zero (mul_ne_zero (X0.yC_ne_zero τ) (pow_ne_zero 2 (x1_ne_zero τ)))
    (one_add_x1_sq_ne_zero τ)

theorem sC_eq (τ : ℍ) : sC τ * x1C τ = x1C τ ^ 2 + 1 := by
  have hq := x1_quad τ
  have : sC τ = 2 * x1C τ - X0.xC τ := by unfold x1C; ring
  rw [this]; linear_combination hq

/-! ## §3. Analyticity and the differential -/

theorem differentiableAt_sC {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ sC σ := by
  have h1 := X0.differentiableAt_yC ⟨σ, hσ⟩
  have h2 := differentiableAt_wC ⟨σ, hσ⟩
  exact h1.neg.div h2 (wC_ne_zero ⟨σ, hσ⟩)

theorem differentiableAt_x1C {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ x1C σ :=
  ((X0.differentiableAt_xC ⟨σ, hσ⟩).add (differentiableAt_sC hσ)).div_const 2

theorem differentiableAt_y1C {σ : ℂ} (hσ : 0 < σ.im) : DifferentiableAt ℂ y1C σ := by
  have h1 := X0.differentiableAt_yC ⟨σ, hσ⟩
  have h2 := differentiableAt_x1C hσ
  exact (h1.mul (h2.pow 2)).div ((differentiableAt_const _).add (h2.pow 2))
    (one_add_x1_sq_ne_zero ⟨σ, hσ⟩)

theorem analyticAt_of_diff {f : ℂ → ℂ} (hf : ∀ σ : ℂ, 0 < σ.im → DifferentiableAt ℂ f σ)
    {σ : ℂ} (hσ : 0 < σ.im) : AnalyticAt ℂ f σ := by
  have hd : DifferentiableOn ℂ f {w : ℂ | 0 < w.im} := fun w hw => (hf w hw).differentiableWithinAt
  exact hd.analyticAt (ZInQ.GZWeil.U_open.mem_nhds hσ)

/-- `dx₁/dτ = 2 y₁ · 2πi f₁`. -/
theorem hasDerivAt_x1C {σ : ℂ} (hσ : 0 < σ.im) :
    HasDerivAt x1C (2 * y1C σ * (2 * Real.pi * I * X0.fC σ)) σ := by
  set τ : ℍ := ⟨σ, hσ⟩
  have hx : HasDerivAt X0.xC (4 * Real.pi * I * X0.fC σ * X0.yC σ) σ :=
    ZInQ.GZWeil.etaModelDifferential τ
  have hs := (differentiableAt_sC hσ).hasDerivAt
  set s' := deriv sC σ
  -- `2 s s' = 2 x x'` from `s² = x² + 4` near `σ`
  have hev : (fun z => sC z ^ 2) =ᶠ[𝓝 σ] (fun z => X0.xC z ^ 2 + 4) := by
    filter_upwards [ZInQ.GZWeil.U_open.mem_nhds hσ] with z hz
    exact sC_sq ⟨z, hz⟩
  have h1 : HasDerivAt (fun z => sC z ^ 2) (2 * sC σ * s') σ := by
    have := hs.pow 2; convert this using 1; push_cast; ring
  have h2 : HasDerivAt (fun z => X0.xC z ^ 2 + 4)
      (2 * X0.xC σ * (4 * Real.pi * I * X0.fC σ * X0.yC σ)) σ := by
    have := (hx.pow 2).add_const 4; convert this using 1; push_cast; ring
  have hss : 2 * sC σ * s' = 2 * X0.xC σ * (4 * Real.pi * I * X0.fC σ * X0.yC σ) :=
    (h1.congr_of_eventuallyEq hev.symm).unique h2
  have hd := (hx.add hs).div_const 2
  have hgoal : (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') / 2 =
      2 * y1C σ * (2 * Real.pi * I * X0.fC σ) := by
    have hq := x1_quad τ
    have hse := sC_eq τ
    have hden := one_add_x1_sq_ne_zero τ
    have hx1 : x1C σ = (X0.xC σ + sC σ) / 2 := rfl
    have key : (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') * (1 + x1C σ ^ 2) =
        2 * (4 * Real.pi * I * X0.fC σ * X0.yC σ) * x1C σ ^ 2 := by
      have hse' : sC σ * x1C σ = x1C σ ^ 2 + 1 := hse
      linear_combination x1C σ * hss / 2 - (4 * Real.pi * I * X0.fC σ * X0.yC σ + s') * hse' -
        (4 * Real.pi * I * X0.fC σ * X0.yC σ) * x1C σ * 2 * hx1
    have hden' : 1 + x1C σ ^ 2 ≠ 0 := hden
    unfold y1C
    field_simp
    linear_combination key
  unfold x1C
  exact hd.congr_deriv hgoal

/-! ## §4. The periods of `Φ₁` over `Γ₀(32) ∩ {(2/d) = 1}` lie in every lattice of `C₁` -/

/-- `x₁` is invariant under the `γ ∈ Γ₀(32)` with `(2/d) = 1`. -/
theorem x1C_inv (hW : EtaW32Character) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32)
    (hχ : ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) = 1) (τ : ℍ) : x1C ((γ • τ : ℍ) : ℂ) = x1C τ := by
  have hinv := ZInQ.Contrib.TYZGenus.Shimura.etaModelInvariant γ hγ τ
  have hv := hW γ hγ τ
  rw [hχ] at hv
  simp only [Int.cast_one, one_mul] at hv
  have hw : wC ((γ • τ : ℍ) : ℂ) = wC τ := by rw [wC_eq_inv, wC_eq_inv, hv]
  unfold x1C sC
  rw [hinv.1, hinv.2, hw]

/-- **The periods of `Φ₁` over the `γ ∈ Γ₀(32)` with `(2/d) = 1` lie in every period lattice of
`C₁ : y² = x³ − x`** (`g₂ = 4`, `g₃ = 0`), given the eta-quotient transformation law for `w`. -/
theorem period_mem_C1 (hW : EtaW32Character) {L : PeriodPair} (hg2 : L.g₂ = 4) (hg3 : L.g₃ = 0)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 32) (hχ : ZMod.χ₈ ((γ 1 1 : ℤ) : ZMod 8) = 1) (τ : ℍ) :
    eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 τ ∈ L.lattice := by
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  refine period_mem_gen L (A := -1) (B := 0) (by rw [hg2]; ring) (by rw [hg3]; ring)
    ZInQ.GZWeil.U_open (X := x1C) (Y := y1C) (Φ := eichlerCd 1)
    (F := fun σ => 2 * Real.pi * I * X0.fC σ)
    (fun σ hσ => analyticAt_of_diff (fun _ h => differentiableAt_x1C h) hσ)
    (fun σ hσ => analyticAt_of_diff (fun _ h => differentiableAt_y1C h) hσ)
    (fun σ hσ => analyticAt_const.mul (ZInQ.GZWeil.analyticAt_fC hσ))
    (fun σ hσ => ZInQ.GZWeil.hasDerivAt_eichlerCd_one hσ)
    (fun σ hσ => hasDerivAt_x1C hσ)
    (fun σ hσ => by have := y1_sq ⟨σ, hσ⟩; simp only at this; rw [this]; ring)
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun σ hσ => mul_ne_zero hpi (X0.fC_ne_zero ⟨σ, hσ⟩))
    ⟨τ, τ.im_pos, y1_ne_zero τ⟩ (g := moeb γ) (fun σ hσ => ZInQ.GZWeil.im_moeb_pos γ hσ)
    (fun σ hσ => by
      have := x1C_inv hW hγ hχ ⟨σ, hσ⟩
      rwa [ZInQ.GZWeil.coe_smul_eq_moeb] at this)
    (fun σ hσ => by
      have := ZInQ.GZWeil.period_const hγ ⟨σ, hσ⟩ τ
      rw [ZInQ.GZWeil.coe_smul_eq_moeb] at this
      simp only at this
      linear_combination this)

/-! ## §5. The twist: `Λ_d ⊆ L` -/

open ZInQ.GZTheta (jacobiChar jacobiChar_natCast jacobiChar_sq_unit)

/-- gz-weil's `period_identity`, with the entries of the `γ'_a`: for `γ ∈ Γ₀(32 d²)`,
`γ 1 0 = 32 d² k`, there are `γ'_a ∈ SL₂(ℤ)` with `γ'_a 1 0 = γ 1 0`,
`γ'_a 0 0 = γ 0 0 + a·d·32k`, `γ'_a 1 1 = γ 1 1 − t_a·d·32k`, and
`d (Φ_d(γτ) − Φ_d(τ)) = Σ_a 𝓕χ_d(a) (Φ₁(γ'_a τ'_a) − Φ₁(τ'_a))`. -/
theorem period_identity' (d : ℕ) [NeZero d] {γ : SL(2, ℤ)}
    {k : ℤ} (hk : γ 1 0 = 32 * d ^ 2 * k) (τ : ℍ) :
    ∃ (γ' : ZMod d → SL(2, ℤ)) (τ' : ZMod d → ℍ) (t : ZMod d → ℤ),
      (∀ a, γ' a 1 0 = γ 1 0) ∧ (∀ a, γ' a 0 0 = γ 0 0 + (a.val : ℤ) * d * (32 * k)) ∧
      (∀ a, γ' a 1 1 = γ 1 1 - t a * d * (32 * k)) ∧ t 0 = 0 ∧
      (d : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)) =
        ∑ a : ZMod d, 𝓕 (jacobiChar d) a *
          (eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ)) := by
  have hc : γ 1 0 = d * d * (32 * k) := by rw [hk]; ring
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
  have hex : ∀ a : ZMod d, ∃ γ' : SL(2, ℤ), γ' 0 0 = γ 0 0 + (a.val : ℤ) * d * (32 * k) ∧
      γ' 1 0 = γ 1 0 ∧ γ' 1 1 = γ 1 1 - (((a * D ^ 2).val : ℕ) : ℤ) * d * (32 * k) ∧
      upperRightHom (((a.val : ℤ) : ℝ) / d) * mapGL ℝ γ =
        mapGL ℝ γ' * upperRightHom (((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) := fun a =>
    TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom γ hc (by
      rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  choose γ' hγ'0 hγ'1 hγ'2 hγ'eq using hex
  set τ' : ZMod d → ℍ := fun a => ((((((a * D ^ 2).val : ℕ) : ℤ) : ℝ) / d) +ᵥ τ) with hτ'
  refine ⟨γ', τ', fun a => (((a * D ^ 2).val : ℕ) : ℤ), hγ'1, hγ'0, hγ'2, by simp, ?_⟩
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
  rw [mul_sub, ZInQ.GZWeil.twist_formula d hz, ZInQ.GZWeil.twist_formula d τ.im_pos,
    ← Finset.sum_sub_distrib]
  have hre : ∑ b : ZMod d, 𝓕 (jacobiChar d) b * eichlerCd 1 ((τ : ℂ) + (b.val : ℂ) / d) =
      ∑ a : ZMod d, 𝓕 (jacobiChar d) a * eichlerCd 1 ((τ' a : ℍ) : ℂ) := by
    refine (Fintype.sum_equiv (Units.mulRight v) _ _ fun a => ?_).symm
    simp only [Units.mulRight_apply, hτ', UpperHalfPlane.coe_vadd]
    rw [ZInQ.GZWeil.dft_mul_unit d (jacobiChar d) v hχv a, hvD]
    congr 2
    push_cast
    ring
  rw [Finset.sum_sub_distrib, hre, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hmove a, mul_sub]

/-- `ρ(δ γ) = ρ(δ) + ρ(γ)` at the base point: `Φ₁(γ τ) − Φ₁(γ' τ) = Φ₁(δ σ) − Φ₁(σ)`,
`δ = γ γ'⁻¹`, `σ = γ' τ`. -/
theorem eichler_mul_sub (γ γ' : SL(2, ℤ)) (τ : ℍ) :
    eichlerCd 1 ((γ • τ : ℍ) : ℂ) - eichlerCd 1 ((γ' • τ : ℍ) : ℂ) =
      eichlerCd 1 (((γ * γ'⁻¹) • (γ' • τ) : ℍ) : ℂ) - eichlerCd 1 ((γ' • τ : ℍ) : ℂ) := by
  rw [← mul_smul, inv_mul_cancel_right]

theorem sum_dft_jacobiChar_eq_zero {d : ℕ} [NeZero d] (hd : 1 < d) :
    ∑ a : ZMod d, 𝓕 (jacobiChar d) a = 0 := by
  have h := ZInQ.GZWeil.sum_dft_mul_stdAddChar d (jacobiChar d) 0
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one] at h
  rw [h, ZInQ.GZTheta.jacobiChar_apply, ZMod.val_zero, Nat.cast_zero, jacobiSym.zero_left hd]
  simp

/-- **`Λ_d ⊆ L` for every period lattice `L` of `C_d`** (`d ≡ 1 mod 4` squarefree, `d > 1`), given the
eta-quotient transformation law (`EtaW32Character`). This sharpens gz-weil's `2 Λ_d ⊆ L`. -/
theorem LamCd_le_of_etaW32 (hW : EtaW32Character) {d : ℕ} (hd4 : d % 4 = 1) (hd1 : 1 < d)
    (hsq : Squarefree d) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) : LamCd d ≤ L.lattice := by
  have : NeZero d := ⟨by omega⟩
  set g := ZInQ.GZWeil.gaussD d with hgdef
  have hg : g ≠ 0 := ZInQ.GZWeil.gaussD_ne_zero hd4 hsq
  have hg2 : g ^ 2 = d := ZInQ.GZWeil.gaussD_sq hd4 hsq
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  obtain ⟨h2, h3⟩ := (ZInQ.GZWeil.isPeriodLattice_cd_iff d L).mp hL
  set L₁ := ZInQ.GZWeil.scalePP L g hg with hL₁
  have hL₁2 : L₁.g₂ = 4 := by
    rw [ZInQ.GZWeil.g₂_scalePP, h2]
    have : g ^ 4 = (d : ℂ) ^ 2 := by rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, hg2]
    rw [this]; field_simp
  have hL₁3 : L₁.g₃ = 0 := by rw [ZInQ.GZWeil.g₃_scalePP, h3, mul_zero]
  rw [LamCd, Submodule.span_le]
  rintro w ⟨γ, hγ, τ, rfl⟩
  obtain ⟨k, hk, hodd⟩ := gamma0_data hγ
  obtain ⟨γ', τ', t, h10, h00, h11, ht0, heq⟩ := period_identity' d hk τ
  -- each period of `Φ₁` at `γ'_a`, moved to the base point `τ`
  have hbase : ∀ a, eichlerCd 1 ((γ' a • τ' a : ℍ) : ℂ) - eichlerCd 1 (τ' a : ℂ) =
      eichlerCd 1 ((γ' a • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ) := by
    intro a
    have hγa : γ' a ∈ Gamma0 32 := by
      rw [Gamma0_mem, h10 a, hk]; push_cast
      rw [show (32 : ZMod 32) = 0 from rfl]; ring
    exact ZInQ.GZWeil.period_const hγa (τ' a) τ
  -- `ρ(γ'_a) − ρ(γ'_0) ∈ L₁`
  have hdiff : ∀ a, (eichlerCd 1 ((γ' a • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) -
      (eichlerCd 1 ((γ' 0 • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) ∈ L₁.lattice := by
    intro a
    have e : (eichlerCd 1 ((γ' a • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) -
        (eichlerCd 1 ((γ' 0 • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) =
        eichlerCd 1 ((γ' a • τ : ℍ) : ℂ) - eichlerCd 1 ((γ' 0 • τ : ℍ) : ℂ) := by ring
    rw [e, eichler_mul_sub]
    set δ := γ' a * (γ' 0)⁻¹ with hδ
    have hδ10 : δ 1 0 = γ 1 0 * (γ' 0 1 1 - γ' a 1 1) := by
      rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [h10]; ring
    have hδ11 : δ 1 1 = -(γ 1 0 * γ' 0 0 1) + γ' a 1 1 * γ' 0 0 0 := by
      rw [hδ, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      simp [h10]
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
    have hδΓ : δ ∈ Gamma0 32 := by
      rw [Gamma0_mem, hδ10, hk]; push_cast
      rw [show (32 : ZMod 32) = 0 from rfl]; ring
    have hδχ : ZMod.χ₈ ((δ 1 1 : ℤ) : ZMod 8) = 1 := by
      have e1 : δ 1 1 = 1 + 8 * (γ 0 1 * 4 * d ^ 2 * k - 4 * d ^ 2 * k * γ' 0 0 1 -
          t a * d * 4 * k * γ 0 0) := by
        rw [hδ11, h11 a, h00 0, hk]
        simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, add_zero]
        linear_combination hdet + (γ 0 1) * hk
      rw [e1]; push_cast
      rw [show (8 : ZMod 8) = 0 from rfl, zero_mul, add_zero, map_one]
    exact period_mem_C1 hW hL₁2 hL₁3 hδΓ hδχ (γ' 0 • τ)
  choose m hmL hmeq using fun a => (ZInQ.GZWeil.mem_scalePP hg).mp (hdiff a)
  set ρ0 := eichlerCd 1 ((γ' 0 • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)
  have hsum0 := sum_dft_jacobiChar_eq_zero hd1
  have key : eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ) =
      ∑ a : ZMod d, ((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * m a := by
    have e1 : eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ) =
        (d : ℂ)⁻¹ * ((d : ℂ) * (eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ))) := by
      field_simp
    rw [e1, heq]
    simp_rw [hbase]
    have e2 : ∑ a : ZMod d, 𝓕 (jacobiChar d) a *
        (eichlerCd 1 ((γ' a • τ : ℍ) : ℂ) - eichlerCd 1 (τ : ℂ)) =
        ∑ a : ZMod d, 𝓕 (jacobiChar d) a * (g * m a) + (∑ a : ZMod d, 𝓕 (jacobiChar d) a) * ρ0 := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hmeq a]; ring
    rw [e2, hsum0, zero_mul, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ZInQ.GZWeil.dft_jacobiChar hd4 hsq, ZInQ.GZTheta.jacobiChar_apply]
    calc (d : ℂ)⁻¹ * (((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * g * (g * m a))
        = (d : ℂ)⁻¹ * (((jacobiSym ((a.val : ℕ) : ℤ) d : ℤ) : ℂ) * g ^ 2 * m a) := by ring
      _ = _ := by rw [hg2]; field_simp
  rw [SetLike.mem_coe, key]
  refine Submodule.sum_mem _ fun a _ => ?_
  have := Submodule.smul_mem L.lattice (jacobiSym ((a.val : ℕ) : ℤ) d) (hmL a)
  rwa [zsmul_eq_mul] at this

end ZInQ.CdOpt
