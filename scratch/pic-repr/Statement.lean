import ZInQKernel.OneProof.H.TailZ24

/-! pic-repr §0: the field's type, copied verbatim from `ZInQKernel/OneProof/H/TailZ24.lean` L289
(`T09Pic.PicRepresentableAbVar`), checked equal by `rfl`. -/

open CategoryTheory AlgebraicGeometry

namespace PicRepr

/-- Verbatim copy of `T09Pic.PicRepresentableAbVar` (LEAF L1 of t09-pic: Murre 1964, Oort 1962;
FGA Exp. 232 Thm 3.1; Kleiman, *The Picard scheme*, Thm 9.4.8 with 9.2.5; UNVERIFIED numbering). -/
def PicRepresentableAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ P : Over (Spec (CommRingCat.of K)), Nonempty ((picardFunctor A.X.hom).obj.RepresentableBy P)

example : PicRepresentableAbVar = T09Pic.PicRepresentableAbVar := rfl

end PicRepr
