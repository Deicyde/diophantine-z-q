/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein (git blob 8ca1784fc060eada9ad57e3f09ebde5558101c13, sha256 7397d11e0ee228a178255eb6fbfb64febb9d0b9b8eab06ad882a185b8d780bec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPins
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal
set_option autoImplicit false

theorem AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      Continuous χ ∧ IsUnitaryChar (𝓞 F) F χ ∧ IsIdeleClassChar (𝓞 F) F χ ∧
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
        ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧
          ∀ s : ℂ, 1 < s.re →
            (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Nc s =
            ∑' ξ : {ξ : F // ξ ≠ 0},
              whittakerCoefficient F (productionPins F) ψ
                (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein.solution
