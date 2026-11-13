import ZInQKernel.HDecomp.Objects
import Mordell.AbelianVariety.Reduction.Basic

/-! Actual point-group base change for the PkgI3 consumer.
No Tate freeness, dimension, semisimplicity or Galois comparison is assumed here. -/

namespace AxiomBridge

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

variable {k : Type} [Field k] (A : PkgI3.AbVar k)
    (L : Type) [Field L] [Algebra k L]

/-- The original L-points are the rational points of the actual pullback group.
This is the multiplicative map/pullback adjunction, not a replacement object. -/
noncomputable def pointsBaseChangeMulEquiv :
    A.Pt L ≃* (𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ (A.baseChange L).X) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap k L))
  exact Faltings.mapPullbackAdjMulEquiv f (Grp.mk A.X)
    (𝟙_ (Over (Spec (CommRingCat.of L))))

/-- The inverse is pinned to the actual first projection of the fibre product. -/
theorem pointsBaseChangeMulEquiv_symm_left
    (x : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ (A.baseChange L).X) :
    ((pointsBaseChangeMulEquiv A L).symm x).left =
      x.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
  exact Faltings.mapPullbackAdjMulEquiv_symm_left _ (Grp.mk A.X) _ x

/-- The original point domain is exactly the image of the unit object over L. -/
theorem mapUnit_eq_ptObj :
    (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj
      (𝟙_ (Over (Spec (CommRingCat.of L)))) = PkgI3.AbVar.ptObj (K := k) L := rfl

/-- Base change commutes with postcomposition by an actual scheme morphism. -/
theorem pointsBaseChangeMulEquiv_natural {B : PkgI3.AbVar k}
    (g : A.X ⟶ B.X) (x : A.Pt L) :
    pointsBaseChangeMulEquiv B L (x ≫ g) =
      pointsBaseChangeMulEquiv A L x ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g := by
  change (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv
      (𝟙_ (Over (Spec (CommRingCat.of L)))) B.X (x ≫ g) =
    (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv
      (𝟙_ (Over (Spec (CommRingCat.of L)))) A.X x ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g
  exact (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv_naturality_right
    (X := 𝟙_ (Over (Spec (CommRingCat.of L)))) (Y := A.X) (Y' := B.X) x g

/-- The same naturality square for the actual PkgI3 abelian-variety Hom action. -/
theorem pointsBaseChangeMulEquiv_ptMap {B : PkgI3.AbVar k}
    (g : PkgI3.AbVar.Hom A B) (x : A.Pt L) :
    pointsBaseChangeMulEquiv B L (PkgI3.AbVar.ptMap g x) =
      pointsBaseChangeMulEquiv A L x ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g.hom :=
  pointsBaseChangeMulEquiv_natural A L g.hom x

/-- The inverse square uses the very same pullback morphism and original Hom. -/
theorem pointsBaseChangeMulEquiv_symm_natural {B : PkgI3.AbVar k}
    (g : A.X ⟶ B.X)
    (x : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ (A.baseChange L).X) :
    (pointsBaseChangeMulEquiv B L).symm
      (x ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map g) =
        (pointsBaseChangeMulEquiv A L).symm x ≫ g := by
  exact (Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap k L)))).homEquiv_naturality_right_symm x g

end AxiomBridge
