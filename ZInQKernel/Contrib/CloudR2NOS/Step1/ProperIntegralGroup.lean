/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/ProperIntegralGroup.lean (sha256 4010827df50f941b3f9f83e1a412d8e8c220b5426294d5d5586fe69f5faa72b1).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: the INTERNAL smoothness-free class for the extracted subvariety `Y`.
2026-11-17. New file (interface v2, lead-approved 03:31Z). SOURCE-ONLY, UNCOMPILED. Universe u.

`IsProperIntegralGroup Y` means proper and geometrically integral, with no smoothness. It is an
INTERNAL binder only:
* E3 PROVES it for the extracted `Y` (GM3.lean);
* it never appears as a premise of the final theorem;
* `IsAbelianVariety ⇒ IsProperIntegralGroup` is an instance.
-/
import ZInQKernel.HDecomp.Objects
import PureMathlibGlobalFunctions

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- A proper, geometrically integral group object over a field (no smoothness). -/
class IsProperIntegralGroup {K : Type u} [Field K] (Y : Grp (Over (Spec (CommRingCat.of K)))) :
    Prop where
  proper : IsProper Y.X.hom
  geomIntegral : GeometricallyIntegral Y.X.hom

instance {K : Type u} [Field K] (Y : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety Y] : IsProperIntegralGroup Y :=
  ⟨PkgI2.IsAbelianVariety.proper, PkgI2.IsAbelianVariety.geomIntegral⟩

theorem isIntegral_of_isProperIntegralGroup {K : Type u} [Field K]
    (Y : Grp (Over (Spec (CommRingCat.of K)))) [IsProperIntegralGroup Y] : IsIntegral Y.X.left := by
  haveI : GeometricallyIntegral Y.X.hom := IsProperIntegralGroup.geomIntegral
  exact GeometricallyIntegral.isIntegral_of_subsingleton Y.X.hom

/-- `Γ(Spec K) → Γ(Y, O_Y)` is bijective (PMGF at the identity section). -/
theorem appTop_bijective_of_isProperIntegralGroup {K : Type u} [Field K]
    (Y : Grp (Over (Spec (CommRingCat.of K)))) [IsProperIntegralGroup Y] :
    Function.Bijective Y.X.hom.appTop := by
  haveI : IsProper Y.X.hom := IsProperIntegralGroup.proper
  haveI : IsIntegral Y.X.left := isIntegral_of_isProperIntegralGroup Y
  exact ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions.appTop_bijective
    Y.X.hom (η[Y.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X).left
    (Over.w (η[Y.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X))

end ZInQ.Contrib.CloudR2NOS.Step1
