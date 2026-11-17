/-
H5 lane3 Step 1: I4 discharged by C4's delivered producer theorem. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED.

The producer is `ZInQ.Contrib.CloudR2NOS.ClosedSection.eulerChar_twist_invariant`, in
lane4-suppliedmodel-converse/patches/ZInQKernel/Contrib/CloudR2NOS/ClosedSection/EulerCharTwist.lean,
sha256 80cef9ff…. It is Source-only, uncompiled, and reports no remaining sub-gap.

C4's `ClosedSection.transl` has the body `letI : GrpObj A.X := A.grp; (lift … ≫ μ[A.X]).left`. That
is the same term as `Step1.transl`, because `Grp.grp` is an instance; the two constants agree by
`rfl` (`transl_eq_closedSection`). No renaming is needed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.Interfaces
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.EulerCharTwist

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem transl_eq_closedSection {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (z : Pt K ⟶ A.X) : transl A z = ZInQ.Contrib.CloudR2NOS.ClosedSection.transl A z := rfl

/-- I4, from C4's producer theorem. -/
theorem eulerCharTwistInvariant : EulerCharTwistInvariant.{u} := by
  intro K _ _ A _ M N _ _ z
  have h := ZInQ.Contrib.CloudR2NOS.ClosedSection.eulerChar_twist_invariant A M N z
  simpa only [twist, transl_eq_closedSection] using h

end ZInQ.Contrib.CloudR2NOS.Step1
