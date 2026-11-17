/-
H5 lane3 Step 1: I1 status v3. With C4's `FieldBaseChangeFreeDirectImage` delivered, I1 rests on
I0 ALONE. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.

The producer, by exact path/SHA, is
`ZInQ.Contrib.CloudR2NOS.ClosedSection.FieldBaseChange.fieldBaseChangeFreeDirectImage`, in
lane4-suppliedmodel-converse/patches/ZInQKernel/Contrib/CloudR2NOS/ClosedSection/FieldBaseChange.lean,
sha256 72a0546d…. It proves exactly `Step1.FieldBaseChangeFreeDirectImage` (R1Core.lean 83fae2f4).

`stabilizer_finite_of_I0` is the agreed I1 from the seam's `χ ≠ 0` and I0 only. It is an
INTERMEDIATE status theorem; I0 remains C2's proof goal.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1StatusV2
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.FieldBaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem stabilizer_finite_of_I0 (hI0 : ExistsFBSLine.{u})
    {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    [PkgI2.IsAbelianVariety Hs] (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (hχ : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
           Ms.eulerChar k) ≠ 0) :
    (stabilizerSet Hs Ms).Finite :=
  stabilizer_finite_of_I0_FB hI0
    ZInQ.Contrib.CloudR2NOS.ClosedSection.FieldBaseChange.fieldBaseChangeFreeDirectImage Hs Ms hχ

end ZInQ.Contrib.CloudR2NOS.Step1
