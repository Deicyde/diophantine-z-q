import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
open AlgebraicGeometry CategoryTheory Limits
example {X S : Scheme} (f : X ⟶ S) (s : S) : f.finrank s =
    (pullback.snd f (S.affineOpenCover.f (S.affineOpenCover.idx s))).appTop.hom.finrank
      ((S.affineOpenCover.X (S.affineOpenCover.idx s)).isoSpec.hom (S.affineOpenCover.covers s).choose) := rfl
#print RingHom.finrank
#print Module.rankAtStalk
