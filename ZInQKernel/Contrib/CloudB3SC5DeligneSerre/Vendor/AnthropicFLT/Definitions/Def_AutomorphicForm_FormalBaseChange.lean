/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_FormalBaseChange (git blob d6ff6ee31473ef1ad2542a26c41a70cb151085fc, sha256 9972c9aa595f8d58eafa6a09c69ded3da6afe19dda4214085599991a7edb2713).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_HeckeEigensystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace AutomorphicForm

section FormalLift

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
  {R : Type*} [CommRing R]

def formalBaseChange (π : HeckeEigensystem F R) : HeckeEigensystem K R where
  level := ⊤
  level_ne_bot := by simp
  a := fun 𝔓 => satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
    (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F)))
  b := fun 𝔓 => (π.b (𝔓.under (𝓞 F))) ^
    ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

@[simp] theorem formalBaseChange_a (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).a 𝔓 =
      satakePow ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)
        (π.a (𝔓.under (𝓞 F))) (π.b (𝔓.under (𝓞 F))) := rfl

@[simp] theorem formalBaseChange_b (π : HeckeEigensystem F R)
    (𝔓 : HeightOneSpectrum (𝓞 K)) :
    (formalBaseChange F K π).b 𝔓 =
      (π.b (𝔓.under (𝓞 F))) ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal) := rfl

end FormalLift

section CubicHypothesis

variable (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def CubicResidueDegOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 1 ∨
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal = 3

def IsDegreeThreeOutside (S : Finset (HeightOneSpectrum (𝓞 K))) : Prop :=
  ∀ 𝔓 : HeightOneSpectrum (𝓞 K), 𝔓 ∉ S →
    (𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ 3

end CubicHypothesis

section Package

variable (R : Type*) [CommRing R]
  (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

structure JPSSCubicLiftPackage where

  notion : CuspidalityNotion R

  cubicDeg : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), IsDegreeThreeOutside F K S

  lift_automorphic : ∀ π : HeckeEigensystem F R, notion.IsCusp F π →
    ∃ Φ : HeckeEigensystem K R, IsBaseChangeOf π Φ ∧
      (notion.IsCusp K Φ ∨ Φ.IsConstantOnFibers F)

end Package

end AutomorphicForm

end
