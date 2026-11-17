/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq (git blob 4a06f9b18718097cf80a50c31a8b92eda601b352, sha256 80627e3370a5dd4d9b72846527d6bb0a9894c54251c968bacb9f56752c7e5954).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain

theorem NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
    (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : AdeleRing (𝓞 F) F → ℂ) (g : (w : InfinitePlace F) → w.Completion → ℂ)
        (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (_hf : IsFactorizableStandardOutside f S g h)
        (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχc : Continuous χ) (_hχu : IsUnitaryChar (𝓞 F) F χ)
        (_hχS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (s : ℂ) (_hs : 1 < s.re),
        zetaIntegral ν f χ s
            * ∏' v : {v // v ∉ S},
                (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))
          = c * (∏ w, LanglandsTunnell.TateLocal.localZeta (μa w) (g w) (archLocalChar χ w) s)
              * ∏ v ∈ S, LanglandsTunnell.TateLocal.localZeta (μf v) (h v) (localChar χ v) s := by
  revert F ν S μf μa ϖ hϖ
  exact @_root_.P2MW.S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.solution
