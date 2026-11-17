/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 (Step 3): the I2 ⇒ I3 assembly with sub-gap (G7) DISCHARGED by the proved
`PresentationBasics.presentationOfIso`. SOURCE ONLY, UNCOMPILED. Native HELD.
Remaining explicit hypotheses: (G1)–(G6) of `Step3Gaps.lean`.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Assembly
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection

local notation "FBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections

/-- **Step 3 on the SAME stage, with (G7) proved.** -/
theorem step3_I3_of_G1_G6
    (hG1 : PresentationTwistIso.{u}) (hG2 : FiniteBySectionsNativePow.{u})
    (hG3 : UniformizerSequence.{u}) (hG4 : FramesNearOfPullback.{u})
    (hG5 : PresentationOfFramesNear.{u}) (hG6 : QuasiFiniteOnClosedFibre.{u})
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (H : Grp (Over (Spec (CommRingCat.of C)))) [PkgI2.IsAbelianScheme H]
    (M : H.X.left.Modules) [M.IsInvertible]
    (hI2 :
      let s := IsLocalRing.closedPoint C
      let k : Type u := (Spec (CommRingCat.of C)).residueField s
      let g := (Spec (CommRingCat.of C)).fromSpecResidueField s
      let Hs := (Over.pullback g).mapGrp.obj H
      let Ms := (Scheme.Modules.pullback (H.X.hom.fiberι s)).obj M
      ∃ b : ℕ, 0 < b ∧ FBS (R := k) (Ms.tensorPow b) Hs.X.hom) :
    ∃ a : ℕ, 0 < a ∧ FBS (M.tensorPow a) H.X.hom :=
  step3_I3 hG1 hG2 hG3 hG4 hG5 hG6 PresentationBasics.presentationOfIso H M hI2

end ZInQ.Contrib.CloudR2NOS.ClosedSection
