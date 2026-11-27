import ZInQKernel.Contrib.OneProof.CMHeight62.Assembly
import ZInQKernel.Contrib.OneProof.CMHeight62.Germ
import ZInQKernel.Contrib.OneProof.CMHeight62.Short
import ZInQKernel.Contrib.OneProof.CMHeight62.Analysis
import ZInQKernel.Contrib.OneProof.CMHeight62.Covolume

/-! # cmheight62-p1: the archimedean identity (steps 1, 2, 4), proved

At every `σ : L → ℂ`, for a metrized model `M` of `E_L` (any smooth group model) and a period
`τ_σ` of `E` at `σ|_K`:

* `coeff_σ(η_W) = k/(c u)` (`k` from the period comparison, `c` the scale of the period lattice of
  `E`, `u` the scale of the short coordinates), by the evaluation bridge and `−2℘/℘' = w + O(w³)`;
* `Λ_σ = (c/k)(ℤ + τℤ)`, so `covol Λ_σ = |c/k|² Im τ`;
* hence `‖η_W‖_σ² = Im τ/|u|²`, and with `σ(Δ_W) = u¹² Δ(τ)`:
  `|σ Δ_W| · ‖η_W‖_σ¹² = |Δ(τ)| (Im τ)⁶`.

This proves `ArchIdentity`, hence the exact formula (step 6) unconditionally, and
`CMHeight62` from `Step7` alone. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace ZInQ.Contrib.CMHeight62

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice Filter Topology IsLocalRing
open _root_.ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization)
open HDec.CMBranch.CMjBridges
open scoped UpperHalfPlane

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
  {E : PkgI3.AbVar K}

/-- The line `w ↦ (w)` in `ℂ¹`. -/
def ι1 : ℂ →L[ℂ] (Fin 1 → ℂ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ

theorem ι1_apply (w : ℂ) : ι1 w = fun _ => w := rfl

theorem ι1_one : ι1 1 = Pi.single 0 1 := by
  funext i; fin_cases i; rfl

/-- `w ↦ F(w)` for `F = germAlong Φ t`. -/
def fOf (𝒢 : GroupModel E L) {σ : L →+* ℂ} (Φ : (Fin 1 → ℂ) → 𝒢.Pts σ) (t : 𝒢.genStalk) :
    ℂ → ℂ := fun w => 𝒢.germAlong Φ t (ι1 w)

/-- `jacDet` in dimension one. -/
theorem jacDet_one (𝒢 : GroupModel E L) {σ : L →+* ℂ} (Φ : (Fin 1 → ℂ) → 𝒢.Pts σ)
    (f : maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ ![f] = fderiv ℂ (𝒢.germAlong Φ (f : 𝒢.genStalk)) 0 (Pi.single 0 1) := by
  simp [GroupModel.jacDet, Matrix.det_unique]

/-- The value `Φ(0)` lies over `ξ`. -/
theorem model_one_apply (𝒢 : GroupModel E L) {σ : L →+* ℂ} :
    (1 : 𝒢.Pts σ).left (ptc σ) = 𝒢.genericUnit := by
  have h := congrArg (fun f => f (ptc σ)) (gpt_fst 𝒢 (1 : 𝒢.Pts σ))
  have h' : (fstGF 𝒢) (gpt 𝒢 1 (ptc σ)) = (1 : 𝒢.Pts σ).left (ptc σ) := h
  rw [← h', gpt_one_apply]
  exact fst_genericFibreUnit 𝒢

theorem zero_mem_dom (𝒢 : GroupModel E L) {σ : L →+* ℂ} {Λ : Submodule ℤ (Fin 1 → ℂ)}
    {Φ : (Fin 1 → ℂ) → 𝒢.Pts σ} (hΦ : 𝒢.IsAnalyticUniformization σ Λ Φ)
    (U : 𝒢.G.left.Opens) (hU : 𝒢.genericUnit ∈ U) : (0 : Fin 1 → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := (hΦ.2.1 0).mpr Λ.zero_mem
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  have hx : x = ptc σ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [hx]
  show (1 : 𝒢.Pts σ).left (ptc σ) ∈ U
  rw [model_one_apply]
  exact hU

/-- **The archimedean identity at one place.** -/
theorem arch_at (hdim : E.dim = 1) (D : ShortData E) (M : MetrizedModel E L 1) (σ : L →+* ℂ)
    {τ : ℂ} (hτ : 0 < τ.im) (hper : HDec.CMBranch.IsPeriodAt E (σ.comp (algebraMap K L)) τ) :
    M.hodge.coeff σ (D.etaW M.model) ≠ 0 ∧
      ‖σ (algebraMap K L D.W.Δ)‖ * M.hodge.norm σ (D.etaW M.model) ^ 12 =
        ‖CMBranch.discAn τ‖ * τ.im ^ 6 := by
  obtain ⟨Φ, hΦ, hcoeff⟩ := M.arch σ
  obtain ⟨ΛE, ΦE, hE, c, hc, hΛE⟩ := hper
  let τh : ℍ := ⟨τ, hτ⟩
  obtain ⟨k, hk, hpt, hlat, hop⟩ := period_comparison hdim M σ hΦ hE
  obtain ⟨u, hu, hcoords⟩ := short_comparison hdim D (τ := τh) hE hc hΛE
  have hΔ : σ (algebraMap K L D.W.Δ) = u ^ 12 * CMBranch.discAn τ :=
    sigma_W_Δ D (σ := σ.comp (algebraMap K L)) (τ := τh) hu hcoords
  -- openness along `gpt`
  have hopen : ∀ W : (genericFibre L M.model.G).left.Opens,
      IsOpen {z | ⊤ ≤ gpt M.model (Φ z) ⁻¹ᵁ W} := by
    intro W
    have hset : {z | ⊤ ≤ gpt M.model (Φ z) ⁻¹ᵁ W} =
        {z | ⊤ ≤ (ZInQ.Metrization2.chi M.model (Φ z)).left ⁻¹ᵁ (M.model.gen.inv.left ⁻¹ᵁ W)} := by
      ext z
      simp only [Set.mem_ofPred_eq, top_le_preimage_iff]
      rw [gpt_eq]
      rfl
    rw [hset]
    exact hop _
  have hb := germAlong_mul_y D M.model hΦ hopen
  -- the function of one variable
  -- `F` is differentiable at `0`
  have hFd : DifferentiableAt ℂ (M.model.germAlong Φ (D.tG M.model : M.model.genStalk)) 0 := by
    have m := (M.model.exists_rep (D.tG M.model : M.model.genStalk)).choose_spec.choose
    have h0 := zero_mem_dom M.model hΦ _ m
    have hdiff := hΦ.2.2.2.2 _ (M.model.exists_rep (D.tG M.model : M.model.genStalk)).choose_spec.choose_spec.choose
    exact (hdiff 0 h0).differentiableAt ((hΦ.2.2.2.1 _).mem_nhds h0)
  have hfc : ContinuousAt (fOf M.model Φ (D.tG M.model : M.model.genStalk)) 0 := by
    have : DifferentiableAt ℂ (fOf M.model Φ (D.tG M.model : M.model.genStalk)) 0 := by
      have h := hFd
      rw [show (0 : Fin 1 → ℂ) = ι1 0 by simp] at h
      exact h.comp (0 : ℂ) ι1.differentiableAt
    exact this.continuousAt
  -- the eventual identity
  set a : ℂ := k / c
  have ha : a ≠ 0 := div_ne_zero hk hc
  set P := PeriodPair.ofTau τh
  have hlatP : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ P.lattice := by
    have hd : IsDiscrete (P.lattice : Set ℂ) :=
      isDiscrete_iff_discreteTopology.mpr (inferInstanceAs (DiscreteTopology P.lattice))
    obtain ⟨ε, hε, hball⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hd
      P.lattice.zero_mem
    have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ Metric.ball (0 : ℂ) ε :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hε)
    filter_upwards [hev, self_mem_nhdsWithin] with w hw hw0 hwl
    have : w ∈ Metric.ball (0 : ℂ) ε ∩ (P.lattice : Set ℂ) := ⟨hw, hwl⟩
    rw [hball] at this
    exact hw0 this
  have hmulA : Tendsto (fun w : ℂ => a * w) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun w : ℂ => a * w) (𝓝 0) (𝓝 (a * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact mul_ne_zero ha hw
  have hmulA' : Tendsto (fun w : ℂ => a * w) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun w : ℂ => a * w) (𝓝 0) (𝓝 (a * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rwa [mul_zero] at this
  have hι : Tendsto ι1 (𝓝 0) (𝓝 0) := by
    have := ι1.continuous.tendsto 0
    rwa [map_zero] at this
  have hb' : ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      ⊤ ≤ (ptL E σ (ZInQ.Metrization2.chi M.model (Φ (ι1 w)))).left ⁻¹ᵁ abVarPunctured E →
        fOf M.model Φ (D.tG M.model : M.model.genStalk) w * cEvalAt (ptL E σ (ZInQ.Metrization2.chi M.model (Φ (ι1 w)))) (abVarPunctured E) D.y =
          -cEvalAt (ptL E σ (ZInQ.Metrization2.chi M.model (Φ (ι1 w)))) (abVarPunctured E) D.x :=
    (hι.eventually hb).filter_mono nhdsWithin_le_nhds
  have hden : ∀ᶠ w in 𝓝[≠] (0 : ℂ), denψ P (a * w) ≠ 0 :=
    (hmulA'.eventually (eventually_denψ_ne_zero P)).filter_mono nhdsWithin_le_nhds
  have heq : ∀ᶠ w in 𝓝[≠] (0 : ℂ),
      fOf M.model Φ (D.tG M.model : M.model.genStalk) w = ψ P u (a * w) := by
    filter_upwards [hb', hden, hmulA.eventually hlatP, hmulA.eventually self_mem_nhdsWithin]
      with w hbw hdw hlw hnw
    have hpw : ptL E σ (ZInQ.Metrization2.chi M.model (Φ (ι1 w))) = ΦE (fun _ => c * (a * w)) := by
      rw [hpt]
      congr 1
      funext i
      simp only [ι1_apply, Pi.smul_apply, smul_eq_mul, a]
      field_simp
    obtain ⟨hpunct, hx, hy⟩ := hcoords (a * w) hlw
    rw [hpw] at hbw
    have hbw' := hbw hpunct
    rw [hx, hy] at hbw'
    have hw0 : a * w ≠ 0 := hnw
    have hd' := dwp_ne_zero P hw0 hdw
    rw [← ratio_eq_ψ P u hw0 hdw]
    have hG : fOf M.model Φ (D.tG M.model : M.model.genStalk) w *
        (u * P.derivWeierstrassP (a * w)) = -2 * P.weierstrassP (a * w) :=
      mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination 2 * hbw')
    rw [eq_div_iff (mul_ne_zero hu hd')]
    exact hG
  have hderiv := hasDerivAt_of_eventually_ψ P hu hfc heq
  -- `coeff = a / u`
  have hcoeffval : M.hodge.coeff σ (D.etaW M.model) = a / u := by
    have h1 : M.hodge.coeff σ (D.etaW M.model) = M.model.jacDet Φ ![D.tG M.model] := hcoeff ![D.tG M.model]
    rw [h1, jacDet_one]
    have h2 : HasDerivAt (fOf M.model Φ (D.tG M.model : M.model.genStalk))
        (fderiv ℂ (M.model.germAlong Φ (D.tG M.model : M.model.genStalk)) 0 (ι1 1)) 0 := by
      have hF : HasFDerivAt (M.model.germAlong Φ (D.tG M.model : M.model.genStalk))
          (fderiv ℂ (M.model.germAlong Φ (D.tG M.model : M.model.genStalk)) 0) (ι1 0) := by
        rw [map_zero]; exact hFd.hasFDerivAt
      exact (hF.comp (0 : ℂ) ι1.hasFDerivAt).hasDerivAt
    rw [← ι1_one]
    exact h2.unique hderiv
  -- covolume
  have hcov : ZLattice.covolume (M.hodge.periods σ) = ‖c / k‖ ^ 2 * τ.im := by
    have := M.hodge.periods_discrete σ
    have := M.hodge.periods_isZLattice σ
    apply covolume_eq_of_mem_iff hτ (div_ne_zero hc hk)
    intro z
    rw [hlat, hΛE]
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨m, n, h⟩; exact ⟨m, n, by field_simp; rw [mul_comm, h]⟩
    · rintro ⟨m, n, h⟩; exact ⟨m, n, by rw [h]; field_simp⟩
  refine ⟨by rw [hcoeffval]; exact div_ne_zero ha hu, ?_⟩
  have hnorm2 : M.hodge.norm σ (D.etaW M.model) ^ 2 = τ.im / ‖u‖ ^ 2 := by
    rw [HodgeData.norm, mul_pow, Real.sq_sqrt (by rw [hcov]; positivity), hcov, hcoeffval]
    simp only [a, norm_div]
    have hk' : ‖k‖ ≠ 0 := norm_ne_zero_iff.mpr hk
    have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    field_simp
  have h12 : M.hodge.norm σ (D.etaW M.model) ^ 12 = (τ.im / ‖u‖ ^ 2) ^ 6 := by
    rw [← hnorm2]; ring
  rw [h12, hΔ, norm_mul, norm_pow]
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  field_simp

/-- **`ArchIdentity`, proved.** -/
theorem archIdentity : ArchIdentity := by
  intro K _ _ L _ _ _ E hdim D M τ hτ
  obtain ⟨σ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  refine ⟨fun h0 => (arch_at hdim D M σ₀ (hτ σ₀).1 (hτ σ₀).2).1 ?_, fun σ =>
    (arch_at hdim D M σ (hτ σ).1 (hτ σ).2).2⟩
  rw [h0, map_zero]

/-- **Step 6, unconditional: the exact height formula for every smooth model.** -/
theorem finrank_mul_modelHeight_eq_exact' (hdim : E.dim = 1) (D : ShortData E)
    (M : MetrizedModel E L 1) (τ : (L →+* ℂ) → ℂ)
    (hτ : ∀ σ, 0 < (τ σ).im ∧ HDec.CMBranch.IsPeriodAt E (σ.comp (algebraMap K L)) (τ σ)) :
    ∃ hη : D.etaW M.model ≠ 0,
      (Module.finrank ℚ L : ℝ) * M.hodge.modelHeight =
        ∑ σ : L →+* ℂ, CMBranch.summand62 (τ σ) +
          (1 / 12) * (Real.log |(Algebra.norm ℚ (algebraMap K L D.W.Δ) : ℝ)| -
            12 * Real.log (FractionalIdeal.absNorm
              (ZInQ.Contrib.RC53Assist.HodgeLatticeIdeal.coefficientFractionalIdeal M.model hdim
                (D.etaW M.model) hη) : ℝ)) :=
  finrank_mul_modelHeight_eq_exact archIdentity hdim D M τ hτ

/-- **`CMHeight62` from step 7.** -/
theorem cmHeight62_of_step7' (h7 : Step7) : HDec.CMBranch.CMHeight62 :=
  cmHeight62_of_step7 archIdentity h7

end ZInQ.Contrib.CMHeight62
