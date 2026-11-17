/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet (git blob 7f3beaff1cfa5dfe664d30aebc797870ad8a8cf1, sha256 7cbaac5c73ceae21d685236835686312b2886e4bf34796f785fe4a924a81d5c0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Φ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level → v ∉ R.exceptionalSet → ‖Φ.b v‖ = 1) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level → v ∉ R.exceptionalSet →
        Φ.a v ^ 2 ≠ Φ.b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹) ∧
        ∃ α β : ℂ, α + β = Φ.a v ∧ α * β = Φ.b v ∧
          ‖α‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
          ‖β‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  revert F c u d₁ d₂ T hc hd₁ hd hcov Φ R hR hb
  exact @_root_.P2MW.S_LanglandsTunnell_satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet.solution
