import ZInQKernel.Contrib.CloudB3W17bIdentity.Section
import ZInQKernel.Contrib.CloudB3W17bProjectiveBridge.OkaAdapter

/-!
# The projectivity object and the comparison object are the same Oka object

`ZInQ.Contrib.CloudB3W17bProjectiveBridge.abVarLiftedLFT B` and
`ZInQ.Contrib.CloudB3W17bOkaComparison.abVarAnalytificationScheme B` are both the original scheme
`B.X.left` with structure map `B.X.hom ≫ complexULiftBaseIso.hom`; they are equal by `rfl`, so the
proved projectivity transfers to the object the global analytic map targets.
-/

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudB3W17bOkaComparison ZInQ.Contrib.CloudB3W17bProjectiveBridge

set_option autoImplicit false

namespace ZInQ.Contrib.CloudB3W17bIdentity

/-- The two Oka objects of the original `B` coincide definitionally. -/
theorem abVarLiftedLFT_eq_abVarAnalytificationScheme (B : PkgI3.AbVar ℂ) :
    abVarLiftedLFT B = abVarAnalytificationScheme B := rfl

/-- The comparison object of the original `B` is projective in Oka's sense. -/
theorem abVarAnalytificationScheme_isProjective (B : PkgI3.AbVar ℂ) :
    ComplexAnalytic.IsProjectiveℂ (abVarAnalytificationScheme B) :=
  abVarLiftedLFT_isProjective B

end ZInQ.Contrib.CloudB3W17bIdentity
