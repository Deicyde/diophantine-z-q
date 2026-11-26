import ZInQKernel.Contrib.OneProof.ConradAppB.Assembly
import ZInQKernel.Contrib.OneProof.ConradAppB.PeriodInduction
import ZInQKernel.Contrib.OneProof.ConradAppB.UnramifiedPeriod
import ZInQKernel.Contrib.OneProof.ConradAppB.Splitting

/-!
# Finite inertia for characters with a weight-zero period, proved

The rank-one weight-zero case of Sen's theorem (Serre, *Groupes algébriques associés aux
modules de Hodge–Tate*, Astérisque 65 (1979), §1.4, Th. 2 and Cor. 3), for every prime `p`,
with all three inputs proved.
-/

set_option autoImplicit false

namespace ZInQ.Contrib.SenWeightZero

/-- **Finite inertia from a weight-zero period**, for every prime. -/
theorem senFiniteInertia_proof : SenFiniteInertia :=
  senFiniteInertia_of_inputs unramifiedCyclotomicSplitting_proof unramifiedPeriod_proof
    periodInduction_proof

end ZInQ.Contrib.SenWeightZero
