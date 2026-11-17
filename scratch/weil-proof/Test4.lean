import ZInQKernel.Contrib.OneProof.WeilFormulaTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilProof.Theta
open PicDict PkgI3 PkgI3.AbVar MonoidalCategory Scheme.Modules PicDict.Transport
open scoped CategoryTheory.MonObj
variable {k : Type} [Field k]

example (X : AbVar k) (L : X.X.left.Modules) (m t s : X.X.left ⟶ X.X.left) (h : t ≫ m = m) (hb : m ≫ t = s ≫ m)
    (hab : t ≫ s = s ≫ t) :
    thetaT h ((Scheme.Modules.pullback t).obj L) ≫ rhoAB hb L =
        (Scheme.Modules.pullback t).map (rhoAB hb L) ≫ swapAB hab ((Scheme.Modules.pullback m).obj L) ≫
          (Scheme.Modules.pullback s).map (thetaT h L) := theta_rho h hb hab L

example (X : AbVar k) (n : ℕ) (y : AC.Kpt X) (L : X.X.left.Modules) (h : (AC.tr (y ^ n)).left ≫ (AC.mul X n).left = (AC.mul X n).left)
    (hb : (AC.mul X n).left ≫ (AC.tr (y ^ n)).left = (AC.tr y).left ≫ (AC.mul X n).left)
    (hab : (AC.tr (y ^ n)).left ≫ (AC.tr y).left = (AC.tr y).left ≫ (AC.tr (y ^ n)).left) :
    thetaT h ((Scheme.Modules.pullback (AC.tr (y ^ n)).left).obj L) ≫ rhoAB hb L =
        (Scheme.Modules.pullback (AC.tr (y ^ n)).left).map (rhoAB hb L) ≫ swapAB hab ((Scheme.Modules.pullback (AC.mul X n).left).obj L) ≫
          (Scheme.Modules.pullback (AC.tr y).left).map (thetaT h L) := theta_rho h hb hab L
