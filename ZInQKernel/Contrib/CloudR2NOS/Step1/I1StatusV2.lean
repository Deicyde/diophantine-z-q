/-
H5 lane3 Step 1: the I1 status assembly v2. I1 now rests on TWO producer obligations. 2026-11-17.
New file. SOURCE-ONLY, UNCOMPILED.

`stabilizer_finite_of_I0_FB` is the agreed I1 (`(stabilizerSet Hs Ms).Finite` from `χ(Ms) ≠ 0`)
with ONLY two hypotheses:
* I0 `ExistsFBSLine` (C2);
* `FieldBaseChangeFreeDirectImage` (C4; R1Core.lean 83fae2f4).
Everything else is a proved term of this lane or a delivered producer term, assembled in
I1Status.lean and R1Small.lean. This is an INTERMEDIATE status theorem, not a final theorem.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1Status
import ZInQKernel.Contrib.CloudR2NOS.Step1.R1Small

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem stabilizer_finite_of_I0_FB (hI0 : ExistsFBSLine.{u})
    (hFB : FieldBaseChangeFreeDirectImage.{u})
    {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    [PkgI2.IsAbelianVariety Hs] (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (hχ : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
           Ms.eulerChar k) ≠ 0) :
    (stabilizerSet Hs Ms).Finite :=
  stabilizer_finite_of_remaining hI0 (relativeVanishingSectionsCore_of hFB)
    (relativeDetectionSections_of hFB) Hs Ms hχ

end ZInQ.Contrib.CloudR2NOS.Step1
