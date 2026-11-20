/-
H5 lane C3 STEP-F21 fix edition (2026-11-17). Source only. The change relative to its base is recorded in the C3 fix ledger.
-/
/-
H5 lane3 Step 2: WIRING of every delivered producer term into B1, B2 and B3. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Producers plugged in, by exact names:
* C4, namespace `ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small`, files under lane4
  …/ClosedSection/Step2Small/:
  - B1Small (hash in ledger): `supportComponentsFinite`, `translationPermutesComponents`, `comapInvertible`;
  - B1HeightOne (hash in ledger): `invertibleSupportNeUniv`;
  - MumfordSmall (hash in ledger): `pointTranslation`, `pointInversion`,
    `rationalPointsDetermineClosed`, `irreducibleInComponent`, `pointsOfSupportInComponents`;
  - B2Small (hash in ledger): `pairedSupportUnion`, `sectionDichotomySupport`, `infinitePointsOfNotFinite`;
  - B3Small (hash in ledger): `presentationFramesEverywhere`, `projSpaceMapSurjective`, `framesNearOfSum`.
* C5 (lane5): `GM3Geometry.geomIrreducibleOverAlgClosed` (hash in ledger) and
  `GM3Geometry.universallyOpenOverField` (hash in ledger).
* C4 B2.a/B2.b and C2 I5a, through AssemblyV2.

The ONLY remaining hypotheses, each a frozen Prop with its producer:
* `hKa : CodimOneLocalizationsDetermine` (C5);
* `hL3 : HeightOneLocalizationDVR` and `hL4 : OffSupportLocalizationTop` (C2);
* `hFS : FromSpecImageCompat` (small; proposed for C4);
* `hPur : PurityTranslateEquality` (C5);
* `hInt : IntegralOnIrreducible` (C4's `isIntegral_subscheme_vanishingIdeal`, adaptation pending);
* `hSpan : PulledSectionsSpan` (C4, in progress).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.L1b
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.HeightOneMax
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.AssemblyV2
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Mumford
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MinkowskiMap
import ZInQKernel.Contrib.CloudR2NOS.Step2B3.FieldDescent
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.B1Small
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.B1HeightOne
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.MumfordSmall
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.B2Small
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.B3Small
import ZInQKernel.Contrib.CMSerreTateSupport.GM3GeometricallyIrreducible
import ZInQKernel.Contrib.CMSerreTateSupport.GM3UniversallyOpenOverField

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.CloudR2NOS.Step2Wiring

open ZInQ.Contrib.CloudR2NOS ZInQ.Contrib.CloudR2NOS.Step2B1 ZInQ.Contrib.CloudR2NOS.Step2B2
  ZInQ.Contrib.CloudR2NOS.Step2B3


/-- B1 (`FiniteSupportStabilizer`) from the remaining external inputs. -/
theorem finiteSupportStabilizer_wired (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u})
    (hFS : FromSpecImageCompat.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u} :=
  finiteSupportStabilizer
    (componentFixingPreservesDivisor hKa
      (fixedComponentLocalizations
        (heightOnePointBehaviour (heightOneMaximalInSupport ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.invertibleSupportNeUniv)
          ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pointsOfSupportInComponents)
        (localizedComapAtHeightOne
          (stalkIdealTransport stalkIdealIndependent (comapLocalizationIso hFS)) hL3 hL4))
      ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.comapInvertible)
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.supportComponentsFinite ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.translationPermutesComponents

/-- B2.d (`MumfordContractedCombinatorics`) from the remaining external inputs. -/
theorem mumfordContractedCombinatorics_wired (hPur : PurityTranslateEquality.{u})
    (hInt : IntegralOnIrreducible.{u}) : MumfordContractedCombinatorics.{u} :=
  mumfordContractedCombinatorics
    (minkowskiIrreducible (minkowskiMap hInt
      H5OriginalDVR.Lane5.GM3Geometry.geomIrreducibleOverAlgClosed
      H5OriginalDVR.Lane5.GM3Geometry.universallyOpenOverField))
    hPur ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pointTranslation ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pointInversion ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.rationalPointsDetermineClosed
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.irreducibleInComponent ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pointsOfSupportInComponents ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.supportComponentsFinite

/-- B2 (`FiniteSquarePresentation`) from the remaining external inputs. -/
theorem finiteSquarePresentation_wired (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u})
    (hFS : FromSpecImageCompat.{u}) (hPur : PurityTranslateEquality.{u})
    (hInt : IntegralOnIrreducible.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u} :=
  finiteSquarePresentation_v2 (mumfordContractedCombinatorics_wired hPur hInt)
    (finiteSupportStabilizer_wired hKa hL3 hL4 hFS)
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.infinitePointsOfNotFinite ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.sectionDichotomySupport ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.pairedSupportUnion

/-- B3 (`NativeFBSFieldDescent`) from the remaining external input. -/
theorem nativeFBSFieldDescent_wired (hSpan : PulledSectionsSpan.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.NativeFBSFieldDescent.{u} :=
  nativeFBSFieldDescent hSpan ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.framesNearOfSum ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.presentationFramesEverywhere
    ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small.projSpaceMapSurjective

end ZInQ.Contrib.CloudR2NOS.Step2Wiring
