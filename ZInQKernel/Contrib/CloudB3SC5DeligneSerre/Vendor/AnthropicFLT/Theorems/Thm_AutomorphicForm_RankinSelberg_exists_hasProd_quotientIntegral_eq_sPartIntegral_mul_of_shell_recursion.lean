/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion (git blob 3df6c7206931ea912f507ebf5d9b9fbfe81c32a2, sha256 f065714bf7e6e89211657019eb88c553589f18504ae8e5f07d639eded088edea).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_HeckeEigenfunction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
      (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
      (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
      (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
      (_hμF : IsIdeleClassChar (𝓞 K) K μ) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (x y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (_hxK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          x (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g)
      (_hyK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          y (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = y g)
      (lx ox ly oy : HeightOneSpectrum (𝓞 K) → ℂ) (κ : ℝ)
      (_hbd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖lx v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖ox v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖ly v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖oy v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
      (_hP : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lx v) (ox v) m *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (ly v) (oy v) m *
            (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1 g)))
      (_hPneg : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0),
    ∃ σ₀ : ℝ, ∀ (s : ℂ), σ₀ < s.re →
      ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ → Continuous φ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
            φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) →
        ∀ (d₁ d₂ : ℝ), Integrable (fun q : RationalCentreUnipotentQuotient K =>
            RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ q.out)
          (rationalCentreUnipotentQuotientMeasure K) →
        ∃ Prod : ℂ,
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            (1 - ox v.1 * oy v.1 *
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ 2) /
              (LanglandsTunnell.RankinSelberg.rsEulerPoly (lx v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * ox v.1)
                  (ly v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * oy v.1) 0).eval
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ 2)) Prod ∧
          RankinSelberg.quotientIntegral K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ =
            RankinSelberg.sPartIntegral K S (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ * Prod := by
  revert K
  exact @_root_.P2MW.S_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion.solution
