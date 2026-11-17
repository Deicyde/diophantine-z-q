/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self (git blob 13d8234d56152eb935b6fff2fad17f04ee9f3566, sha256 70e6d0326246595add733e2870fa33fc2fff8d3ca06b4b67029673ea4bc2ba3c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NarrowRayClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply
open scoped Classical

theorem AutomorphicForm.exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ : HeckeEigensystem K ℂ)
    (hΘ : IsArithGenuineCuspRealizable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ S →
      ∃ σ₀ : ℝ, ∃ Λ : ℂ → ℂ,
      (∃ a : ℝ, a < 1 ∧ MeromorphicOn Λ {s : ℂ | a < s.re}) ∧
      meromorphicOrderAt Λ 1 = -1 ∧
      (∀ σ : ℝ, 1 < σ → AnalyticAt ℂ Λ (σ : ℂ)) ∧
      ∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s) := by
  revert K c u d₁ d₂ T hc hd₁ hd hcov Θ hΘ
  exact @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_lt_one_meromorphicOn_meromorphicOrderAt_one_eq_neg_one_analyticAt_hasProd_rsEulerPoly_self.solution
