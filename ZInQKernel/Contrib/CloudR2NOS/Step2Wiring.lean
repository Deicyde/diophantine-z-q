/-
H5 lane3 Step 2: WIRING of every delivered producer term into B1, B2 and B3. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Producers plugged in, by exact names:
* C4, namespace `ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small`, files under lane4
  …/ClosedSection/Step2Small/:
  - B1Small 52c20b22: `supportComponentsFinite`, `translationPermutesComponents`, `comapInvertible`;
  - B1HeightOne ffa23822: `invertibleSupportNeUniv`;
  - MumfordSmall 0dec6cb0: `pointTranslation`, `pointInversion`,
    `rationalPointsDetermineClosed`, `irreducibleInComponent`, `pointsOfSupportInComponents`;
  - B2Small b2591d2a: `pairedSupportUnion`, `sectionDichotomySupport`, `infinitePointsOfNotFinite`;
  - B3Small 5a6fabe6: `presentationFramesEverywhere`, `projSpaceMapSurjective`, `framesNearOfSum`.
* C5 (lane5): `GM3Geometry.geomIrreducibleOverAlgClosed` b991b2dc and
  `GM3Geometry.universallyOpenOverField` 43a445b9.
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
import GM3GeometricallyIrreducible
import GM3UniversallyOpenOverField

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.CloudR2NOS.Step2Wiring

open ZInQ.Contrib.CloudR2NOS ZInQ.Contrib.CloudR2NOS.Step2B1 ZInQ.Contrib.CloudR2NOS.Step2B2
  ZInQ.Contrib.CloudR2NOS.Step2B3

local notation "C4" => ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

/-- B1 (`FiniteSupportStabilizer`) from the remaining external inputs. -/
theorem finiteSupportStabilizer_wired (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u})
    (hFS : FromSpecImageCompat.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u} :=
  finiteSupportStabilizer
    (componentFixingPreservesDivisor hKa
      (fixedComponentLocalizations
        (heightOnePointBehaviour (heightOneMaximalInSupport C4.invertibleSupportNeUniv)
          C4.pointsOfSupportInComponents)
        (localizedComapAtHeightOne
          (stalkIdealTransport stalkIdealIndependent (comapLocalizationIso hFS)) hL3 hL4))
      C4.comapInvertible)
    C4.supportComponentsFinite C4.translationPermutesComponents

/-- B2.d (`MumfordContractedCombinatorics`) from the remaining external inputs. -/
theorem mumfordContractedCombinatorics_wired (hPur : PurityTranslateEquality.{u})
    (hInt : IntegralOnIrreducible.{u}) : MumfordContractedCombinatorics.{u} :=
  mumfordContractedCombinatorics
    (minkowskiIrreducible (minkowskiMap hInt
      H5OriginalDVR.Lane5.GM3Geometry.geomIrreducibleOverAlgClosed
      H5OriginalDVR.Lane5.GM3Geometry.universallyOpenOverField))
    hPur C4.pointTranslation C4.pointInversion C4.rationalPointsDetermineClosed
    C4.irreducibleInComponent C4.pointsOfSupportInComponents C4.supportComponentsFinite

/-- B2 (`FiniteSquarePresentation`) from the remaining external inputs. -/
theorem finiteSquarePresentation_wired (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u})
    (hFS : FromSpecImageCompat.{u}) (hPur : PurityTranslateEquality.{u})
    (hInt : IntegralOnIrreducible.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u} :=
  finiteSquarePresentation_v2 (mumfordContractedCombinatorics_wired hPur hInt)
    (finiteSupportStabilizer_wired hKa hL3 hL4 hFS)
    C4.infinitePointsOfNotFinite C4.sectionDichotomySupport C4.pairedSupportUnion

/-- B3 (`NativeFBSFieldDescent`) from the remaining external input. -/
theorem nativeFBSFieldDescent_wired (hSpan : PulledSectionsSpan.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.NativeFBSFieldDescent.{u} :=
  nativeFBSFieldDescent hSpan C4.framesNearOfSum C4.presentationFramesEverywhere
    C4.projSpaceMapSurjective

end ZInQ.Contrib.CloudR2NOS.Step2Wiring
