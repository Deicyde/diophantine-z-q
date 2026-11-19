/-
H5 lane3 Step 2, B2 assembly v2. C4's B2.a and B2.b, and C2's all-field I5a, are plugged in.
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.

Producers, by exact path/SHA:
* B2.a: `ZInQ.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts.nonFiniteContractsSubvariety`
  (lane4 …/ClosedSection/NonFiniteContracts.lean 6139270f…).
* B2.b: `ZInQ.Contrib.CloudR2NOS.ClosedSection.ContractedTrivial.contractedPresentationTrivial`
  (lane4 …/ClosedSection/ContractedTrivial.lean f7da8580…).
* I5a: `H5OriginalDVR.Lane2.AllFieldNativeSquare.theoremOfSquare` (lane2 a448c099…).
B2 now rests on B2.d (lane3), B1 (lane3) and the three small obligations of Assembly.lean.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.Assembly
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.ContractedTrivial
import AllFieldNativeSquare

set_option autoImplicit false

noncomputable section

universe u

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

theorem finiteSquarePresentation_v2 (hD : MumfordContractedCombinatorics.{u})
    (hB1 : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u})
    (hPts : InfinitePointsOfNotFinite.{u}) (hDS : SectionDichotomySupport.{u})
    (hPU : PairedSupportUnion.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u} :=
  finiteSquarePresentation
    ZInQ.Contrib.CloudR2NOS.ClosedSection.NonFiniteContracts.nonFiniteContractsSubvariety
    ZInQ.Contrib.CloudR2NOS.ClosedSection.ContractedTrivial.contractedPresentationTrivial
    hD hB1 H5OriginalDVR.Lane2.AllFieldNativeSquare.theoremOfSquare hPts hDS hPU

end ZInQ.Contrib.CloudR2NOS.Step2B2
