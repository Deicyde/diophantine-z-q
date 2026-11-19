/-
H5 lane3 Step 2: WIRING v2. `FromSpecImageCompat` is discharged (FromSpecCompat.lean 620e40ea).
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
Remaining inputs: `hKa` (C5), `hL3`/`hL4` (C2), `hPur` (C5), `hInt` (C4 adaptation), and, for B3,
`hSpan` (C4).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2Wiring
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.FromSpecCompat

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.CloudR2NOS.Step2Wiring

open ZInQ.Contrib.CloudR2NOS.Step2B1 ZInQ.Contrib.CloudR2NOS.Step2B2

theorem finiteSupportStabilizer_wired_v2 (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u} :=
  finiteSupportStabilizer_wired hKa hL3 hL4 fromSpecImageCompat

theorem finiteSquarePresentation_wired_v2 (hKa : CodimOneLocalizationsDetermine.{u})
    (hL3 : HeightOneLocalizationDVR.{u}) (hL4 : OffSupportLocalizationTop.{u})
    (hPur : PurityTranslateEquality.{u}) (hInt : IntegralOnIrreducible.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u} :=
  finiteSquarePresentation_wired hKa hL3 hL4 fromSpecImageCompat hPur hInt

end ZInQ.Contrib.CloudR2NOS.Step2Wiring
