import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.CommutingFiniteBinding
import ActualTameDensityV001

/-!
# Finite inertia for a base-defined CM elliptic curve

The actual ambient tame-generator theorem supplies the literal generator
input directly. Together with the original CM, Frobenius, finite wild-image
and commuting-image proofs, it gives the exact finite-inertia statement.
No further arithmetic, rank, faithfulness or finite-image premise is added.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate.P1

/-- The actual tame-generator theorem has precisely the literal written
input, with the same original wild subgroup and ambient Galois closure. -/
theorem actualTameGeneratorInput_proved : ActualTameGeneratorInput := by
  intro K hK hNF O hO w hw
  exact _root_.ActualTameInertia.exists_tameGeneratorDense K O (AlgebraicClosure K) w hw

/-- The exact original finite-inertia interface for a base-defined CM
elliptic curve, with no added supplier or comparison hypothesis. -/
theorem p1FiniteInertia_proved : HDec.CMSerreTate.P1FiniteInertia :=
  p1FiniteInertia_of_actualTameGenerator actualTameGeneratorInput_proved

end HDec.CMSerreTate.P1
