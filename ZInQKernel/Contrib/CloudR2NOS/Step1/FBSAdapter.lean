/-
H5 lane3 Step 1 (v2; v1 4a9133f9 is in history/): the FBS primitives of FBSRestrict.lean
discharged by their producers. Under interface v2, `FBSUnitFinite` comes from C4's
FBSUnitFiniteV2 (0f585ad3).
plus G6 and FBS restriction with those primitives filled in. 2026-11-17. New file. SOURCE-ONLY,
UNCOMPILED.

Producer: C4 (), `ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics` in
lane4-suppliedmodel-converse/patches/ZInQKernel/Contrib/CloudR2NOS/ClosedSection/PresentationBasics.lean,
sha256 a03eb73c…. Its four statements are verbatim the four Props of FBSRestrict.lean; its local
notations `Pres` and `FBS'` are the same FLT names as `ProjPresentation` and `FBS`.
An equivalent producer of `FBSIsoInvariant` is C5's `H5OriginalDVR.Lane5.GM12.fbsIsoInvariant`
(lane5-dvr-descent/GM12FBSIsoInvariant.lean 1c5c6b1f…), typed directly as
`Step1.FBSIsoInvariant`. Either one closes that Prop.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.FBSRestrict
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.PresentationBasics
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FBSUnitFiniteV2

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem projPresentationPullback_proved : ProjPresentationPullback.{u} :=
  ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.projPresentationPullback

theorem fbsIsoInvariant_proved : FBSIsoInvariant.{u} :=
  ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.fbsIsoInvariant

theorem fbsNonzeroSection_proved : FBSNonzeroSection.{u} :=
  ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.fbsNonzeroSection

/-- v2: from C4's general `fbsUnitFinite_of_appTop_bijective` (FBSUnitFiniteV2.lean 0f585ad3…),
with the internal class. -/
theorem fbsUnitFinite_proved : FBSUnitFinite.{u} := by
  intro K _ _ Y _ hFBS
  haveI : IsProper Y.X.hom := IsProperIntegralGroup.proper
  exact ZInQ.Contrib.CloudR2NOS.ClosedSection.PresentationBasics.fbsUnitFinite_of_appTop_bijective
    Y (appTop_bijective_of_isProperIntegralGroup Y) hFBS

/-- Parent check (1), with no remaining FBS primitive: FBS restricts along a closed immersion. -/
theorem fbs_pullback_closedImmersion {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (j : Y ⟶ X) [IsClosedImmersion j] (N : X.Modules)
    (h : FBS N f) : FBS ((Scheme.Modules.pullback j).obj N) (j ≫ f) :=
  fbs_pullback projPresentationPullback_proved f j N h

/-- G6 from R3, with no remaining FBS primitive. -/
theorem nontrivialTranslateFromR3_proved : NontrivialTranslateFromR3.{u} :=
  nontrivialTranslateFromR3 projPresentationPullback_proved fbsIsoInvariant_proved
    fbsUnitFinite_proved fbsNonzeroSection_proved

end ZInQ.Contrib.CloudR2NOS.Step1
