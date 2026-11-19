/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral (git blob 443af8ac23385b5536b7dad7992c492f84b5b6ca, sha256 e56bd72e7b8107770b1c94d71ec87f3ef4e56e5342ece465bb7f9681cfe54abb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain

noncomputable section

namespace AutomorphicForm

namespace RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type) [Field K] [NumberField K]

def quotientIntegrand (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ({g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
      (fun _ => (1 : ℂ)) g) *
    whittakerCoefficient K pins ψ x 1 g * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 g) * φ g *
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)

def quotientIntegral (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q : RationalCentreUnipotentQuotient K, quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out
    ∂(rationalCentreUnipotentQuotientMeasure K)

def shellZeroOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2}

def sPartIntegral (S : Finset (HeightOneSpectrum (𝓞 K))) (pins : CarrierPins K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (x y φ : AdelicGL2 (𝓞 K) K → ℂ) (w d₁ d₂ : ℝ) : ℂ :=
  ∫ q in {q : RationalCentreUnipotentQuotient K | q.out ∈ shellZeroOutside K S},
    quotientIntegrand K pins ψ x y φ w d₁ d₂ q.out ∂(rationalCentreUnipotentQuotientMeasure K)

end RankinSelberg

end AutomorphicForm

end
