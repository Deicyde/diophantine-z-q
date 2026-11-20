/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Injectivity of the ORIGINAL same-closure O → POrd map is actually derived
from its canonical comapHom field embedding. This supplies BetaFactory's
base input; it is not an additional final NOS assumption or an assumed
injective raw stage leg. Existing field-compatibility proof is reused.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericField
import ZInQKernel.Contrib.CloudR2Raynaud.StrictHenselization.OrdinaryInside

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Original-K/same-closure field embedding supplies the actual injective
    canonical base map into P = w.comap(E → Ω), with no ring replacement. -/
theorem original_ordinary_comap_injective
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    (O : ValuationSubring K) (E : IntermediateField K Ω) (w : ValuationSubring Ω)
    (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O) :
    letI : Algebra O (w.comap (algebraMap E Ω)) :=
      (ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.comapHom hE).toAlgebra
    Function.Injective (algebraMap O (w.comap (algebraMap E Ω))) := by
  letI : Algebra O (w.comap (algebraMap E Ω)) :=
    (ZInQ.Contrib.CloudR2Raynaud.StrictHenselization.comapHom hE).toAlgebra
  exact ZInQ.Contrib.CloudR2NOS.Spreadout.injective_of_comap (fun x => rfl)

#print axioms original_ordinary_comap_injective

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
