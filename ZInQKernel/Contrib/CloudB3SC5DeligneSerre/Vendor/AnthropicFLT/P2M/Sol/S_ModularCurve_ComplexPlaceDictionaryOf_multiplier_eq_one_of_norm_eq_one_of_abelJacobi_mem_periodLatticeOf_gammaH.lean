/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH (git blob ef1b730b59ad0870e5f03cf2158c353fbb659975, sha256 7af7bb7bcff7509ec7e0c5cf32fc959d6639086e310d1ecf514a9766e108234f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLatticeOf_gammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH

set_option autoImplicit false

open scoped MatrixGroups Real Topology
open UpperHalfPlane Filter

namespace ModularCurve
export _root_.ModularCurve (ComplexPlaceDictionaryOf ComplexPlaceDictionary Gamma1_le_GammaH xHFunctionField periodAlongOf periodLatticeOf period exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex ComplexPlaceDictionaryOf.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLatticeOf_gammaH petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH)
namespace UnitaryReciprocityH
open _root_.ModularCurve

theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

theorem tendsto_smul_ofComplex_nhdsNE (γ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) (𝓝[≠] (τ : ℂ))
      (𝓝[≠] ((γ • τ : ℍ) : ℂ)) := by
  have hcont : Tendsto (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) (𝓝 (τ : ℂ))
      (𝓝 ((γ • τ : ℍ) : ℂ)) := by
    have h := (hasDerivAt_smul_ofComplex γ τ).continuousAt.tendsto
    simp only [ofComplex_apply] at h
    exact h
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hcont.mono_left nhdsWithin_le_nhds) ?_
  have hS : {z : ℂ | 0 < z.im} ∈ 𝓝[≠] (τ : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  filter_upwards [hS, self_mem_nhdsWithin] with z hz hne
  rw [Set.mem_compl_singleton_iff] at hne ⊢
  intro habs
  apply hne
  have h1 : γ • ofComplex z = γ • τ := UpperHalfPlane.ext habs
  have h2 : ofComplex z = τ := smul_left_cancel γ h1
  rw [← h2, ofComplex_apply_of_im_pos hz, coe_mk]

section Quot

variable {Γ : Subgroup SL(2, ℤ)} {F F₀ : ℍ → ℂ} {χ χ₀ : Γ → ℂ} {k : ℍ → ℤ}

structure IsMult (F : ℍ → ℂ) (χ : Γ → ℂ) (k : ℍ → ℤ) : Prop where
  mero : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)
  mult : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ
  unit : ∀ γ : Γ, ‖χ γ‖ = 1
  cusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)
  ord : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = ((k τ : ℤ) : WithTop ℤ)

noncomputable def quot (F F₀ : ℍ → ℂ) : ℂ → ℂ :=
  (fun z : ℂ => F (ofComplex z)) / fun z : ℂ => F₀ (ofComplex z)

noncomputable def U (F F₀ : ℍ → ℂ) : ℂ → ℂ := toMeromorphicNFOn (quot F F₀) {z : ℂ | 0 < z.im}

theorem quot_coe (w : ℍ) : quot F F₀ (w : ℂ) = F w / F₀ w := by
  simp only [quot, Pi.div_apply, ofComplex_apply]

theorem quot_apply (z : ℂ) : quot F F₀ z = F (ofComplex z) / F₀ (ofComplex z) := rfl

theorem quot_meromorphicAt (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    MeromorphicAt (quot F F₀) (τ : ℂ) :=
  (h.mero τ).div (h₀.mero τ)

theorem quot_meromorphicOn (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) :
    MeromorphicOn (quot F F₀) {z : ℂ | 0 < z.im} :=
  fun z hz => quot_meromorphicAt h h₀ ⟨z, hz⟩

theorem quot_order (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    meromorphicOrderAt (quot F F₀) (τ : ℂ) = 0 := by
  have h1 := meromorphicOrderAt_div (h.mero τ) (h₀.mero τ)
  rw [h.ord τ, h₀.ord τ, ← WithTop.LinearOrderedAddCommGroup.coe_sub, sub_self,
    WithTop.coe_zero] at h1
  exact h1

theorem U_nf : MeromorphicNFOn (U F F₀) {z : ℂ | 0 < z.im} :=
  meromorphicNFOn_toMeromorphicNFOn _ _

theorem U_eventuallyEq_quot (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    U F F₀ =ᶠ[𝓝[≠] (τ : ℂ)] quot F F₀ :=
  (quot_meromorphicOn h h₀).toMeromorphicNFOn_eq_self_on_nhdsNE τ.im_pos

theorem U_order (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    meromorphicOrderAt (U F F₀) (τ : ℂ) = 0 := by
  rw [meromorphicOrderAt_congr (U_eventuallyEq_quot h h₀ τ)]
  exact quot_order h h₀ τ

theorem U_analyticAt (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    AnalyticAt ℂ (U F F₀) (τ : ℂ) :=
  ((U_nf (F := F) (F₀ := F₀)) τ.im_pos).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (U_order h h₀ τ).ge

theorem U_ne_zero (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    U F F₀ (τ : ℂ) ≠ 0 :=
  ((U_nf (F := F) (F₀ := F₀)) τ.im_pos).meromorphicOrderAt_eq_zero_iff.mp (U_order h h₀ τ)

theorem tendsto_quot (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (τ : ℍ) :
    Tendsto (quot F F₀) (𝓝[≠] (τ : ℂ)) (𝓝 (U F F₀ (τ : ℂ))) :=
  (((U_analyticAt h h₀ τ).continuousAt.tendsto).mono_left nhdsWithin_le_nhds).congr'
    (U_eventuallyEq_quot h h₀ τ)

theorem tendsto_quot_smul (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (σ : SL(2, ℤ)) (τ : ℍ) :
    Tendsto (fun z : ℂ => F (σ • ofComplex z) / F₀ (σ • ofComplex z)) (𝓝[≠] (τ : ℂ))
      (𝓝 (U F F₀ ((σ • τ : ℍ) : ℂ))) := by
  have := (tendsto_quot h h₀ (σ • τ)).comp (tendsto_smul_ofComplex_nhdsNE σ τ)
  refine this.congr fun z => ?_
  simp only [Function.comp_apply, quot_coe]

theorem U_smul (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (γ : Γ)
    (τ : ℍ) :
    U F F₀ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = χ γ / χ₀ γ * U F F₀ (τ : ℂ) := by
  have ha := tendsto_quot_smul h h₀ (γ : SL(2, ℤ)) τ
  have hb : Tendsto (fun z : ℂ => χ γ / χ₀ γ * quot F F₀ z) (𝓝[≠] (τ : ℂ))
      (𝓝 (χ γ / χ₀ γ * U F F₀ (τ : ℂ))) :=
    (tendsto_quot h h₀ τ).const_mul _
  have hfun : (fun z : ℂ => F ((γ : SL(2, ℤ)) • ofComplex z) / F₀ ((γ : SL(2, ℤ)) • ofComplex z))
      = fun z : ℂ => χ γ / χ₀ γ * quot F F₀ z := by
    funext z
    rw [h.mult, h₀.mult, quot_apply, mul_div_mul_comm]
  rw [hfun] at ha
  exact tendsto_nhds_unique ha hb

theorem U_tendsto_atImInfty (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k) (σ : SL(2, ℤ))
    {L L₀ : ℂ} (hL : Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hL₀ : Tendsto (fun τ : ℍ => F₀ (σ • τ)) atImInfty (𝓝 L₀)) (hL₀ne : L₀ ≠ 0) :
    Tendsto (fun τ : ℍ => U F F₀ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 (L / L₀)) := by
  have hH : Tendsto (fun τ : ℍ => F (σ • τ) / F₀ (σ • τ)) atImInfty (𝓝 (L / L₀)) :=
    hL.div hL₀ hL₀ne
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hev : ∀ᶠ τ : ℍ in atImInfty, dist (F (σ • τ) / F₀ (σ • τ)) (L / L₀) < ε / 2 :=
    Metric.tendsto_nhds.mp hH (ε / 2) (half_pos hε)
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  show {τ : ℍ | dist (U F F₀ ((σ • τ : ℍ) : ℂ)) (L / L₀) < ε} ∈ atImInfty
  rw [atImInfty_mem]
  refine ⟨A + 1, fun τ hτ => ?_⟩
  simp only [Set.mem_setOf_eq]

  have hlim := tendsto_quot_smul h h₀ σ τ
  have hS : {z : ℂ | 0 < z.im} ∈ 𝓝[≠] (τ : ℂ) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have hA' : {z : ℂ | A < z.im} ∈ 𝓝[≠] (τ : ℂ) := by
    apply mem_nhdsWithin_of_mem_nhds
    apply (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    show A < (τ : ℂ).im
    rw [coe_im]
    linarith
  have hin : ∀ᶠ z : ℂ in 𝓝[≠] (τ : ℂ),
      F (σ • ofComplex z) / F₀ (σ • ofComplex z) ∈ Metric.closedBall (L / L₀) (ε / 2) := by
    filter_upwards [hS, hA'] with z hz hzA
    have hmem := hA (ofComplex z) (by
      rw [ofComplex_apply_of_im_pos hz]
      show A ≤ z.im
      exact le_of_lt hzA)
    exact Metric.mem_closedBall.mpr (le_of_lt hmem)
  have hmem : U F F₀ ((σ • τ : ℍ) : ℂ) ∈ Metric.closedBall (L / L₀) (ε / 2) :=
    Metric.isClosed_closedBall.mem_of_tendsto hlim hin
  rw [Metric.mem_closedBall] at hmem
  linarith

theorem multiplier_eq [Γ.FiniteIndex] (h : IsMult F χ k) (h₀ : IsMult F₀ χ₀ k)
    (γ : Γ) : χ γ = χ₀ γ := by
  have hχ₀ne : ∀ γ : Γ, χ₀ γ ≠ 0 := by
    intro γ h0
    have := h₀.unit γ
    rw [h0, norm_zero] at this
    exact zero_ne_one this

  set Uh : ℍ → ℂ := fun τ => U F F₀ (τ : ℂ) with hUh
  set ψ : Γ → ℂ := fun γ => χ γ / χ₀ γ with hψ
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => Uh (ofComplex z)) {z : ℂ | 0 < z.im} := by
    have hU : DifferentiableOn ℂ (U F F₀) {z : ℂ | 0 < z.im} := fun z hz =>
      (U_analyticAt h h₀ ⟨z, hz⟩).differentiableAt.differentiableWithinAt
    refine hU.congr fun z hz => ?_
    show U F F₀ ((ofComplex z : ℍ) : ℂ) = U F F₀ z
    rw [ofComplex_apply_of_im_pos hz, coe_mk]
  have hmult : ∀ (γ : Γ) (τ : ℍ),
      Uh ((γ : SL(2, ℤ)) • τ) = ψ γ * Uh τ := fun γ τ => U_smul h h₀ γ τ
  have hunit : ∀ γ : Γ, ‖ψ γ‖ = 1 := by
    intro γ
    show ‖χ γ / χ₀ γ‖ = 1
    rw [norm_div, h.unit, h₀.unit, div_one]
  have hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun τ : ℍ => Uh (σ • τ)) atImInfty (𝓝 L) := by
    intro σ
    obtain ⟨L, hLne, hL⟩ := h.cusp σ
    obtain ⟨L₀, hL₀ne, hL₀⟩ := h₀.cusp σ
    exact ⟨L / L₀, div_ne_zero hLne hL₀ne, U_tendsto_atImInfty h h₀ σ hL hL₀ hL₀ne⟩
  obtain ⟨C, hC⟩ :=
    ModularCurve.exists_eq_const_of_norm_multiplier_eq_one_of_finiteIndex Γ Uh ψ hdiff hmult hunit hcusp
  have hCne : C ≠ 0 := by
    rw [← hC UpperHalfPlane.I]
    exact U_ne_zero h h₀ UpperHalfPlane.I
  have hψ1 : ψ γ = 1 := by
    have hEq : C = ψ γ * C := by
      have h1 := hmult γ UpperHalfPlane.I
      rwa [hC, hC] at h1
    have : (ψ γ - 1) * C = 0 := by rw [sub_mul, one_mul, ← hEq, sub_self]
    rcases mul_eq_zero.mp this with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hCne
  exact (div_eq_one_iff_eq (hχ₀ne γ)).mp hψ1

end Quot

end ModularCurve.UnitaryReciprocityH

open ModularCurve.UnitaryReciprocityH in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0)
    (hΛ : (c.sum fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (F : UpperHalfPlane → ℂ) (χ : CohCarrier.GammaH M H → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : CohCarrier.GammaH M H) (τ : UpperHalfPlane), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : CohCarrier.GammaH M H, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) UpperHalfPlane.atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ) =
      (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : WithTop ℤ))
    (γ : CohCarrier.GammaH M H) : χ γ = 1 := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)

  obtain ⟨F₀, χ₀, f, hF₀, hχ₀, hunit₀, hcusp₀, hord₀, hχ₀f, Λ₀, hΛ₀, hrec⟩ :=
    ModularCurve.ComplexPlaceDictionaryOf.exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLatticeOf_gammaH
      M H D c hdeg

  have h : IsMult F χ (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) :=
    ⟨hF, hχ, hunit, hcusp, hord⟩
  have h₀ : IsMult F₀ χ₀ (fun τ => (D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ)) :=
    ⟨hF₀, hχ₀, hunit₀, hcusp₀, hord₀⟩
  rw [multiplier_eq h h₀ γ, hχ₀f γ]

  have hPet : ∃ Λ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      ∀ g : CuspForm (CohCarrier.GammaH M H) 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
          (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))),
            UpperHalfPlane.petersson 2 ⇑f ⇑g τ) = Λ g := by
    refine ⟨Λ₀ - c.sum (fun τ n => n • ModularCurve.periodAlongOf (CohCarrier.GammaH M H) UpperHalfPlane.I τ),
      Submodule.sub_mem _ hΛ₀ hΛ, fun g => ?_⟩
    rw [LinearMap.sub_apply]
    linear_combination hrec g
  obtain ⟨m, hm⟩ := (ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int_gammaH M H f).mp hPet γ
  rw [hm]
  have : (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I m
