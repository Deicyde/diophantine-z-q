import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.FiniteInertiaConditional
import FrobLift.CommutingFiniteV002

/-!
# The proved commuting-image criterion at its exact input type

The original generic criterion supplies the named commuting-finite input.
All its continuity, wild-image, Frobenius and tame-density arguments are
retained. The actual tame-generator input remains the only premise in the
finite-inertia specialization below.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate.P1

/-- The generic proved criterion has exactly the written consumer type,
including the original wild subgroup and ambient tame-density condition. -/
theorem commutingFiniteInput_proved : CommutingFiniteInput := by
  intro K Ω hK hΩ hAlg hAlgc G hG hTopo hT1 w ρ hρ hFinite φ hD q hCong τ hτ hq hComm hGen
  haveI : Finite (_root_.FrobLift.wildImage ρ w) := hFinite
  change _root_.FrobLift.TameGeneratorDense w τ at hGen
  exact _root_.FrobLift.finite_inertiaImage_of_commute
    (ρ := ρ) (w := w) hρ hD hCong hτ hq hComm hGen

/-- Finite inertia from the actual CM, Frobenius, wild-image and
commuting-image proofs, conditional only on the actual tame generator. -/
theorem p1FiniteInertia_of_actualTameGenerator (hTame : ActualTameGeneratorInput) :
    HDec.CMSerreTate.P1FiniteInertia :=
  p1FiniteInertia_conditional hTame commutingFiniteInput_proved

end HDec.CMSerreTate.P1
