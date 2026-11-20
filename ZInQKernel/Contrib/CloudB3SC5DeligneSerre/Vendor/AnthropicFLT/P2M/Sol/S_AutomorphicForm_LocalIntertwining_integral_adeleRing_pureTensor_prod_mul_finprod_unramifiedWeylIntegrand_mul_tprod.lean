/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod (git blob 2e609782d69c59ff102c8eb928e3e828b017e229, sha256 9b53c32bf9619665905b7352903abb113b5b0e658bd61bf21f41685375d299b4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicBox_inv_measure_adelicBox_mul_integral_pureTensor_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_LocalIntertwining_integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox IsDedekindDomain

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
    [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (v.adicCompletion F)) [∀ v, (μv v).IsAddHaarMeasure]
    (f : mixedEmbedding.mixedSpace F → ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F → ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ)
    (hϖ : ∀ v ∉ S, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ v u = 1)
    (hχ₁ : ∀ v ∉ S, ‖((χ v (ϖ v) : ℂˣ) : ℂ)‖ ≤ 1)
    (s : ℂ) (hs : 1 / 2 < s.re) :
    ((μ (adelicBox F)).toReal : ℂ)⁻¹
        * (∫ x, f (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
              * ((∏ v ∈ S, h v (x.2 v))
                * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                    (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
                        (fun _ => (1 : ℂ)) (x.2 v.1)
                      + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                          (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                          (x.2 v.1)))) ∂μ)
        * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))
      = (((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
        * (∫ y, f y)
        * ((∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
              * ∫ y, h v y ∂(μv v)))
          * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) := by
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h3 := NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq F μ
    (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 F) F)) f
    (fun z : FiniteAdeleRing (𝓞 F) F => (∏ v ∈ S, h v (z v))
      * ∏ᶠ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (((v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)).indicator
              (fun _ => (1 : ℂ)) (z v.1)
            + (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt (χ v.1)⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)))
                (z v.1))))
  have h4 :=
    AutomorphicForm.LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod
      F (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 F) F)) S μv h ϖ hϖ χ hχ hχ₁ s hs
  rw [h3, ← h4]
  unfold Measure.real
  ring

#print axioms solution
