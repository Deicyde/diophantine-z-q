/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_HeckeCharacter_FiniteOrder (git blob 2a6a5dd5d2c96168bd04c6c292c81325cb895f31, sha256 085a4f00adc4a6f830fa89ae31698d905a1106b81f91a3b7a8128b70bea8f95c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain WithZero

noncomputable section

namespace HeckeCharacter

variable (K : Type*) [Field K] [NumberField K]

structure IsFiniteOrderHeckeChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop where
  isIdeleClassChar : IsIdeleClassChar (𝓞 K) K χ
  continuous : Continuous χ
  isOfFinOrder : IsOfFinOrder χ

def idealMultiplicity (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk 𝔣).factors

def AdmitsModulus (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  ∀ u : (AdeleRing (𝓞 K) K)ˣ,
    (u : AdeleRing (𝓞 K) K).1 = 1 →
    (∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      Valued.v ((u : AdeleRing (𝓞 K) K).2 v - 1)
        ≤ WithZero.exp (-(idealMultiplicity K v 𝔣 : ℤ))) →
    χ u = 1

end HeckeCharacter
