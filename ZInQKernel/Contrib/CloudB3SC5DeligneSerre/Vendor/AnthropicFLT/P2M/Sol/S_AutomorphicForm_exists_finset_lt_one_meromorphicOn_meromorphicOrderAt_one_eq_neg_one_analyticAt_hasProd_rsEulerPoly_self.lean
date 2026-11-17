/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self (git blob ce29a748ee02b677583cb101e20bb82581ac7033, sha256 faff9ce94528df787b006fa5ab0a257a4afb27120c20f710dccd2ab2738bb3f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_PeterssonIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_StandardGlobalAddChar
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NarrowRayClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import Mathlib.Analysis.Meromorphic.NormalForm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_RankinSelberg_exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_exists_finset_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open Filter Topology
open AutomorphicForm.CuspidalConstituent
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10P

variable {K : Type} [Field K] [NumberField K]

theorem modulus_pos (t : (AdeleRing (𝓞 K) K)ˣ) :
    0 < ((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits t : ℝˣ) : ℝ) := by
  show 0 < ((distribHaarChar (AdeleRing (𝓞 K) K) t : ℝ≥0) : ℝ)
  exact NNReal.coe_pos.2 (distribHaarChar_pos)

end RS10P

theorem RS40S_rsRep_simple
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) R.centralChar V)
    (hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.level ⊓ archCutSubmodule K tys) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet) ∧
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
        (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
        meromorphicOrderAt Λ 1 = -1 ∧
        (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
        ∀ s : ℂ, σ₀ < s.re →
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
                (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by
  obtain ⟨S, f, φ, w, e₁, e₂, a, σ₀, C, 𝓕, A, L, ζi, hS, -, -, -, -, -, -, -, -, -, ha, hσ₀, hC,
    hA, hAI, hA0, hJ, hJpos, hζ, hζne, hζpos, hL, hprod⟩ :=
    AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_one_half_mul_peterssonIntegral_and_hasProd_rsEulerPoly_self K RS10P.modulus_pos c u d₁ d₂ T hc hd₁ hd hcov Θ R hR tys V hV hRV

  set J : ℂ → ℂ := fun s : ℂ => RankinSelberg.sPartIntegral K S
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (rightConv K R.toFun f) (rightConv K R.toFun f) (φ s) w e₁ e₂
    with hJdef
  set U : Set ℂ := {z : ℂ | a + 1 / 2 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hshift : ∀ z ∈ U, z - 1 / 2 ∈ {s : ℂ | a < s.re} := by
    intro z hz
    have hz' : a + 1 / 2 < z.re := hz
    show a < (z - 1 / 2).re
    have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
    rw [this]; linarith
  have hmaps : Set.MapsTo (fun z : ℂ => z - 1 / 2) U {s : ℂ | a < s.re} := fun z hz => hshift z hz
  have hsub : AnalyticOnNhd ℂ (fun z : ℂ => z - 1 / 2) Set.univ :=
    (analyticOnNhd_id).sub analyticOnNhd_const

  set g : ℂ → ℂ := fun z => A (z - 1 / 2) with hg
  set k : ℂ → ℂ := fun z => C * J (z - 1 / 2) * ζi (z - 1 / 2) with hk
  set h : ℂ → ℂ := fun z => (z - 1) * k z with hh
  have hAsh : AnalyticOnNhd ℂ (fun z : ℂ => A (z - 1 / 2)) U := hA.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hJsh : AnalyticOnNhd ℂ (fun z : ℂ => J (z - 1 / 2)) U := hJ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hζsh : AnalyticOnNhd ℂ (fun z : ℂ => ζi (z - 1 / 2)) U := hζ.comp (hsub.mono (Set.subset_univ _)) hmaps
  have hgan : AnalyticOnNhd ℂ g U := hAsh
  have hkan : AnalyticOnNhd ℂ k U := fun z hz =>
    (analyticAt_const.mul (hJsh z hz)).mul (hζsh z hz)
  have hhan : AnalyticOnNhd ℂ h U := fun z hz =>
    ((analyticAt_id.sub analyticAt_const).mul (hkan z hz))

  have hkreal : ∀ σ : ℝ, a + 1 / 2 < σ → k σ ≠ 0 := by
    intro σ hσ
    have h1 : a < σ - 1 / 2 := by linarith
    have e : ((σ - 1 / 2 : ℝ) : ℂ) = (σ : ℂ) - 1 / 2 := by push_cast; ring
    obtain ⟨-, hJre⟩ := hJpos (σ - 1 / 2) h1
    obtain ⟨-, hζre⟩ := hζpos (σ - 1 / 2) h1
    rw [e] at hJre hζre
    have hJne : J ((σ : ℂ) - 1 / 2) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [Complex.zero_re] at this
      exact hJre.ne' this
    have hζne' : ζi ((σ : ℂ) - 1 / 2) ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [Complex.zero_re] at this
      exact hζre.ne' this
    simp only [hk]
    exact mul_ne_zero (mul_ne_zero hC hJne) hζne'

  set M : ℂ → ℂ := fun z => g z / h z with hM
  have hMmero : MeromorphicOn M U := fun z hz => ((hgan z hz).meromorphicAt).div ((hhan z hz).meromorphicAt)
  set Λ : ℂ → ℂ := toMeromorphicNFOn M U with hΛ
  have hΛNF : MeromorphicNFOn Λ U := meromorphicNFOn_toMeromorphicNFOn M U
  have hΛmero : MeromorphicOn Λ U := hΛNF.meromorphicOn
  have hΛM : ∀ z ∈ U, Λ =ᶠ[𝓝[≠] z] M := fun z hz =>
    (hMmero.toMeromorphicNFOn_eq_self_on_nhdsNE hz)

  have hone : (1 : ℂ) ∈ U := by
    show a + 1 / 2 < (1 : ℂ).re
    simp only [Complex.one_re]; linarith
  have htwo : (2 : ℂ) ∈ U := by
    show a + 1 / 2 < (2 : ℂ).re
    norm_num; linarith
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt (a + 1 / 2)).isPreconnected
  have hk1 : k 1 ≠ 0 := by
    have := hkreal 1 (by linarith)
    simpa using this
  have hh2 : h 2 ≠ 0 := by
    have hk2 := hkreal 2 (by linarith)
    have : h 2 = (2 - 1) * k ((2 : ℝ) : ℂ) := by simp [hh]
    rw [this]
    exact mul_ne_zero (by norm_num) hk2

  have hh_ne : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, h w ≠ 0 := by
    intro z hz
    rcases (hhan z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
    · exfalso
      have hzero := hhan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hz h0
      exact hh2 (hzero htwo)
    · exact hne

  have hMeq : M = g * h⁻¹ := by
    funext z; simp [hM, div_eq_mul_inv]
  have hordM : ∀ z ∈ U, meromorphicOrderAt M z = meromorphicOrderAt g z - meromorphicOrderAt h z := by
    intro z hz
    rw [hMeq, meromorphicOrderAt_mul (hgan z hz).meromorphicAt (hhan z hz).meromorphicAt.inv,
      meromorphicOrderAt_inv, sub_eq_add_neg]
  have hordΛ : ∀ z ∈ U, meromorphicOrderAt Λ z = meromorphicOrderAt M z := fun z hz =>
    meromorphicOrderAt_congr (hΛM z hz)

  have ord0 : ∀ {F : ℂ → ℂ} {z : ℂ}, AnalyticAt ℂ F z → F z ≠ 0 → meromorphicOrderAt F z = 0 := by
    intro F z hF hFz
    rw [hF.meromorphicOrderAt_eq, hF.analyticOrderAt_eq_zero.mpr hFz]
    rfl

  have hg1 : g 1 ≠ 0 := by
    have : g 1 = A (1 / 2) := by simp [hg]; norm_num
    rw [this]
    exact hA0
  have hl1 : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => z - 1) z := fun z => by
    exact ((analyticAt_id (𝕜 := ℂ) (z := z)).sub (analyticAt_const (v := (1 : ℂ))))
  have hordh1 : meromorphicOrderAt h 1 = 1 := by
    have hlin : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff (hl1 1).meromorphicAt]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
    show meromorphicOrderAt ((fun z : ℂ => z - 1) * k) 1 = 1
    rw [meromorphicOrderAt_mul (hl1 1).meromorphicAt (hkan 1 hone).meromorphicAt,
      hlin, ord0 (hkan 1 hone) hk1, add_zero]
    rfl
  have hord : meromorphicOrderAt Λ 1 = -1 := by
    rw [hordΛ 1 hone, hordM 1 hone, ord0 (hgan 1 hone) hg1, hordh1]
    decide

  have han : ∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ) := by
    intro σ hσ
    have hσU : (σ : ℂ) ∈ U := by
      show a + 1 / 2 < (σ : ℂ).re
      simp; linarith
    have hhσ : h σ ≠ 0 := by
      have hkσ := hkreal σ (by linarith)
      show ((σ : ℂ) - 1) * k σ ≠ 0
      refine mul_ne_zero ?_ hkσ
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith

    have hordσ : 0 ≤ meromorphicOrderAt Λ σ := by
      rw [hordΛ σ hσU, hordM σ hσU, ord0 (hhan σ hσU) hhσ, sub_zero]
      exact (hgan σ hσU).meromorphicOrderAt_nonneg
    exact ((hΛNF hσU).meromorphicOrderAt_nonneg_iff_analyticAt).mp hordσ

  have hprodΛ : ∀ z : ℂ, σ₀ + 1 / 2 < z.re →
      HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
        ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
            (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (Λ z) := by
    intro z hz
    have hzU : z ∈ U := by
      show a + 1 / 2 < z.re
      linarith

    have hV : ∀ᶠ w in 𝓝 z, σ₀ + 1 / 2 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    have key : ∀ w : ℂ, σ₀ + 1 / 2 < w.re → h w ≠ 0 → M w = L (w - 1 / 2) := by
      intro w hw hhw
      have hws : σ₀ < (w - 1 / 2).re := by
        have : (w - 1 / 2 : ℂ).re = w.re - 1 / 2 := by simp
        rw [this]; linarith
      have hws' : 1 / 2 < (w - 1 / 2).re := lt_trans hσ₀ hws
      obtain ⟨-, hI⟩ := hprod (w - 1 / 2) hws
      have hAw := hAI (w - 1 / 2) hws'
      have hgw : g w = h w * L (w - 1 / 2) := by
        show A (w - 1 / 2) = (w - 1) * (C * J (w - 1 / 2) * ζi (w - 1 / 2)) * L (w - 1 / 2)
        rw [hAw, hI]
        simp only [hJdef]
        ring
      show g w / h w = L (w - 1 / 2)
      rw [hgw, mul_div_cancel_left₀ _ hhw]
    have hMG : M =ᶠ[𝓝[≠] z] fun w => L (w - 1 / 2) := by
      filter_upwards [hh_ne z hzU, hV.filter_mono nhdsWithin_le_nhds] with w h1 h2
      exact key w h2 h1
    have hGan : AnalyticAt ℂ (fun w => L (w - 1 / 2)) z := by
      refine (hL _ ?_).comp (hsub z trivial)
      show σ₀ < (z - 1 / 2).re
      have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
      rw [this]; linarith
    have hΛG : Λ =ᶠ[𝓝[≠] z] fun w => L (w - 1 / 2) := (hΛM z hzU).trans hMG
    have hΛz : Λ z = L (z - 1 / 2) :=
      (((hΛNF hzU).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hGan.meromorphicNFAt).mp hΛG).eq_of_nhds
    obtain ⟨hP, -⟩ := hprod (z - 1 / 2) (by
      have : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by simp
      rw [this]; linarith)
    simp only [sub_add_cancel] at hP
    rw [hΛz]
    exact hP
  refine ⟨S, hS, σ₀ + 1 / 2, Λ, ⟨a + 1 / 2, by linarith, hΛmero⟩, hord, han, hprodΛ⟩

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open Deep.NTSupply
open scoped Classical

noncomputable section

namespace RS10B

open Polynomial

theorem eval_rsEulerPoly_self_inv_mul (a b N : ℂ) (hb : b ≠ 0) (hN : N ≠ 0) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (a / b) b⁻¹ a b 0).eval N⁻¹ * (b * N ^ 4) =
      (N - 1) ^ 2 * (b * N ^ 2 - (a ^ 2 - 2 * b) * N + b) := by
  simp only [LanglandsTunnell.RankinSelberg.rsEulerPoly, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp
  ring

theorem eval_rsEulerPoly_self_inv_ne_zero (a b N : ℂ) (hN : N ≠ 0) (hN1 : N ≠ 1)
    (hgen : a ^ 2 ≠ b * (N + 2 + N⁻¹)) :
    (LanglandsTunnell.RankinSelberg.rsEulerPoly (a / b) b⁻¹ a b 0).eval N⁻¹ ≠ 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [LanglandsTunnell.RankinSelberg.rsEulerPoly]
  intro h
  have key := eval_rsEulerPoly_self_inv_mul a b N hb hN
  rw [h, zero_mul] at key
  have h2 : (N - 1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hN1)
  have h3 : b * N ^ 2 - (a ^ 2 - 2 * b) * N + b = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd h h2
    · exact h
  apply hgen
  field_simp
  linear_combination -h3

theorem pole0_of_rsrep_gen
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 := by
  obtain ⟨ξ, S₀, tys, V, φ, hV, hφV, hφ0, hiso, hφt⟩ :=
    AutomorphicForm.exists_isCuspConstituent_isIsotypicCuspFormAt_mem_archCutSubmodule_of_isArithGenuineCuspRealizable K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  set R := hiso.toRealization hφ0 with hRdef
  have hR : IsGenuineCuspRealizationAt K _ Θ.toRawCentral R := hiso.continuous
  have hRV : R.toFun ∈ V ⊓ levelInvariantSubmodule K _ Θ.level ⊓ archCutSubmodule K tys :=
    ⟨⟨hφV, hiso.level_invariant⟩, hφt⟩
  obtain ⟨S, hgood, σ₀, Λ, hmero, hord, han, hprod⟩ :=
    RS40S_rsRep_simple K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR tys V hV hRV
  refine ⟨S, σ₀, Λ, hmero, hord, han, hprod, fun v hv => ?_⟩
  obtain ⟨hlv, hex⟩ := hgood v hv
  have hgen := AutomorphicForm.SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet K c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlv hex
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hN1 : Ideal.absNorm v.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  exact eval_rsEulerPoly_self_inv_ne_zero _ _ _ (Nat.cast_ne_zero.mpr hN0) (by exact_mod_cast hN1) hgen

end RS10B

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)) ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        (LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v / Θ.b v) (Θ.b v)⁻¹ (Θ.a v) (Θ.b v) 0).eval
          ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹) ≠ 0 :=
  RS10B.pole0_of_rsrep_gen K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
