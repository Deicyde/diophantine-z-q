/-
H5 lane3 Step 1: ADAPTERS and the I1 status assembly. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED.

Producer terms plugged in, each by exact path/SHA:
* E3, C5 (lane5-dvr-descent):
  - GM3GeometricallyReduced 7b157df6 `GM3Geometry.geomReducedOverAlgClosed`
  - GM3GeometricallyIrreducible b991b2dc `GM3Geometry.geomIrreducibleOverAlgClosed`
  - GM3ClosedOpsOfPoints 3b7f6384 `GM3Points.closedUnderOpsOfPoints`
  - GM3TranslateComponent b4b50a88 `GM3Points.translateComponent`
  - GM3UniversallyOpenOverField 43a445b9 `GM3Geometry.universallyOpenOverField`
* I5a, C2: AllFieldNativeSquare a448c099 `theoremOfSquare`.
* I5b, C2: InversionFromSeesawWeak cad1528d `inversionTranslationInvariant_of_seesaw`, fed with
  this lane's `seesawPulledBack_native` (GM1).
* I4, C4: I4Adapter.
* FBS, C4: FBSAdapter.
* Lane3 proofs: E1, E3a/E3b assemblies, GM1, R2, R3, T, SS and G6.

`stabilizer_finite_of_remaining` is the agreed I1 (`(stabilizerSet Hs Ms).Finite` from the seam's
`χ ≠ 0`). Its ONLY hypotheses are the three still-open obligations:
* I0 `ExistsFBSLine` (C2);
* `RelativeVanishingSectionsCore` (lane3, R1 core);
* `RelativeDetectionSections` (lane3, R1b).
It is an INTERMEDIATE status theorem, not a final theorem. These three remain proof goals.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.StabilizerClosed
import ZInQKernel.Contrib.CloudR2NOS.Step1.IdentityComponent
import ZInQKernel.Contrib.CloudR2NOS.Step1.TensorHomNeZero
import ZInQKernel.Contrib.CloudR2NOS.Step1.FBSAdapter
import ZInQKernel.Contrib.CloudR2NOS.Step1.I4Adapter
import ZInQKernel.Contrib.CloudR2NOS.Step1.HigherProjectionFormula
import ZInQKernel.Contrib.CloudR2NOS.Step1.HigherDirectImageAutomorphism
import GM3GeometricallyReduced
import GM3GeometricallyIrreducible
import GM3ClosedOpsOfPoints
import GM3TranslateComponent
import GM3UniversallyOpenOverField
import AllFieldNativeSquare
import InversionFromSeesawWeak

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- E3, from C5's five producers and this lane's proofs. -/
theorem infiniteClosedSubgroupContainsIntegral_proved :
    InfiniteClosedSubgroupContainsIntegral.{u} :=
  infiniteClosedSubgroupContainsIntegral_of
    (reducedClosedSubgroup_of H5OriginalDVR.Lane5.GM3Points.closedUnderOpsOfPoints
      isReducedSubschemeVanishingIdeal grpObjOfCompatibleMono
      H5OriginalDVR.Lane5.GM3Geometry.geomReducedOverAlgClosed)
    (identityComponentIntegral_final H5OriginalDVR.Lane5.GM3Points.translateComponent
      H5OriginalDVR.Lane5.GM3Geometry.geomReducedOverAlgClosed
      H5OriginalDVR.Lane5.GM3Geometry.geomIrreducibleOverAlgClosed
      H5OriginalDVR.Lane5.GM3Geometry.universallyOpenOverField)

/-- E, from E1 (proved) and E3. -/
theorem infiniteStabilizerExtraction_proved : InfiniteStabilizerExtraction.{u} :=
  infiniteStabilizerExtraction_of_E3 infiniteClosedSubgroupContainsIntegral_proved

/-- I5b, from C2's producer and this lane's GM1. -/
theorem inversionTranslationInvariant_proved : InversionTranslationInvariant.{u} :=
  H5OriginalDVR.Lane2.InversionFromSeesawWeak.inversionTranslationInvariant_of_seesaw
    seesawPulledBack_native

/-- I1 in the agreed form, from the three still-open obligations only (an INTERMEDIATE status
theorem, not a final theorem). -/
theorem stabilizer_finite_of_remaining (hI0 : ExistsFBSLine.{u})
    (hcore : RelativeVanishingSectionsCore.{u}) (hR1b : RelativeDetectionSections.{u})
    {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    [PkgI2.IsAbelianVariety Hs] (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (hχ : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
           Ms.eulerChar k) ≠ 0) :
    (stabilizerSet Hs Ms).Finite :=
  stabilizer_finite_of_parts infiniteStabilizerExtraction_proved hI0 eulerCharTwistInvariant
    H5OriginalDVR.Lane2.AllFieldNativeSquare.theoremOfSquare inversionTranslationInvariant_proved
    seesawPulledBack_native twistSelectionFromSquare seesawShearFromSeesaw
    sectionsVanishFromInversion_proved nontrivialTranslateFromR3_proved
    (relativeVanishingSections hcore) hR1b higherDirectImageAutomorphism Hs Ms hχ

end ZInQ.Contrib.CloudR2NOS.Step1
