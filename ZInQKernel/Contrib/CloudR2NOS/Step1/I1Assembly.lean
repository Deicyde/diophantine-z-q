/-
H5 FIX EDITION STEP-F2 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/I1Assembly.lean (sha256 25a34b357035f2e0c7a3318315963e922323be487cc30e2af70692ef45e3f2fb).
Body change relative to the base: ONLY P4, the line `open scoped CategoryTheory.MonObj` inserted before `namespace` (record step-fix2/FIX_RECORD_STEP_F2.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: the I1 assembly. 2026-11-17, v2. New file. SOURCE-ONLY, UNCOMPILED.

v2 change: every Euler characteristic carries an explicit Over instance; see the I1BaseChange v2
header. v1 71102f91 is kept in `step1-i1/history/`.

The agreed I1 form (step1-i1/I1_AGREED_FORM.md a5998d24…, consumer C2) is proved here from:
* ONE explicit, UNPROVED core gap `CoreGap`, which is the Route-A program;
* the proved I1a;
* the seam's `hEuler`.
`CoreGap` itself is reduced to named parts in `Interfaces.lean`, by `coreGap_of_parts`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1BaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The geometric stabilizer `K(M̄)` of the agreed I1 form. Its elements are `k̄`-points `x` of
`H̄ = PkgI2.baseChange Hs k̄` with `t_x^* M̄ ≅ M̄`, where `t_x` is right translation in the SAME
transported group law. -/
def stabilizerSet {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k))))
    (Ms : Hs.X.left.Modules) :
    Set (𝟙_ (Over (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
      (PkgI2.baseChange Hs (AlgebraicClosure k)).X) :=
  letI : GrpObj (PkgI2.baseChange Hs (AlgebraicClosure k)).X :=
    (PkgI2.baseChange Hs (AlgebraicClosure k)).grp
  {x | Nonempty ((Scheme.Modules.pullback
    (CartesianMonoidalCategory.lift (𝟙 (PkgI2.baseChange Hs (AlgebraicClosure k)).X)
      (CartesianMonoidalCategory.toUnit (PkgI2.baseChange Hs (AlgebraicClosure k)).X ≫ x) ≫
        μ[(PkgI2.baseChange Hs (AlgebraicClosure k)).X]).left).obj (Msbar Hs Ms) ≅ Msbar Hs Ms)}

/-- CORE GAP (UNPROVED as a whole; reduced to parts in `Interfaces.lean`): over `k̄`, an infinite
stabilizer forces `χ(M̄) = 0`. -/
def CoreGap : Prop :=
  ∀ {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety Hs]
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible],
    (stabilizerSet Hs Ms).Infinite →
      (letI : (PkgI2.baseChange Hs (AlgebraicClosure k)).X.left.Over
          (Spec (CommRingCat.of (AlgebraicClosure k))) :=
        ⟨(PkgI2.baseChange Hs (AlgebraicClosure k)).X.hom⟩
       (Msbar Hs Ms).eulerChar (AlgebraicClosure k)) = 0

/-- I1 in the agreed form, from `CoreGap`, the proved I1a, and the seam's `hEuler`. -/
theorem stabilizer_finite_of_eulerChar_ne_zero (hcore : CoreGap.{u}) {k : Type u} [Field k]
    (Hs : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety Hs]
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (hχ : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
           Ms.eulerChar k) ≠ 0) :
    (stabilizerSet Hs Ms).Finite := by
  by_contra hfin
  exact hχ ((eulerChar_Msbar Hs Ms).symm.trans (hcore Hs Ms hfin))

end ZInQ.Contrib.CloudR2NOS.Step1
