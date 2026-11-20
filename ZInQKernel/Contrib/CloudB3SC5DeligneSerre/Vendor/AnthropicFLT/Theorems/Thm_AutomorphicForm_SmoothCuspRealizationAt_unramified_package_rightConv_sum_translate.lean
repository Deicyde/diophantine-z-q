/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate (git blob 68170ac65418dc1f20207c07b18de1ccdba5af3f, sha256 067fd6fefe1c66afdc6e1d7ce44be5e06a209db92b9834bb992a66f3f6eed01c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothCuspRealization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_LocalOrbitalBase
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain

theorem AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sf ⊆ S) (hSψ : Sψ ⊆ S)
    (hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i))
    (hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g)
    (hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh))
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    ((∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)) ∧
    ∃ (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
      (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) =
          ψv xv * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) =
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.a v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.b v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) := by
  revert K c u d₁ d₂ T Θ R hR hRlev f hfT S Sf Sψ hSf hSψ hfsupp hS hSψ0 r h cs hharch hhcomm x hxsum hxint hxper hxZ v hv
  exact @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate.solution
