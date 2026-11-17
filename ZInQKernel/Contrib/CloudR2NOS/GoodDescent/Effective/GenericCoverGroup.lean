/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

The GENERIC restriction of the actual cartesian GROUP identification,
using the already published explicit pbNat components and Lane3's proved
monoidal-natural-transformation law. Actual projection equations are
proved, not guessed from nominally similar pullback isomorphisms.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericBaseChange

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open ZInQ.Contrib.SpreadOut

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Group version of the published EXPLICIT cartesian composition iso. -/
def pbNatGroupIso {S U T : Scheme.{u}} (a : T ⟶ U) (b : U ⟶ S) (c : T ⟶ S)
    (h : a ≫ b = c) (D : Grp (Over S)) :
    (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj D) ≅
      (Over.pullback c).mapGrp.obj D := by
  let D₁ := (Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj D)
  let D₂ := (Over.pullback c).mapGrp.obj D
  letI : GrpObj ((Over.pullback b ⋙ Over.pullback a).obj D.X) := D₁.grp
  letI : GrpObj ((Over.pullback c).obj D.X) := D₂.grp
  let E : D₁.X ≅ D₂.X := (pbNat a b c h).app D.X
  haveI : IsMonHom E.hom := ZInQ.Contrib.CloudR2NOS.Spreadout.isMonHom_app_comp
    (F := Over.pullback b) (G := Over.pullback a) (H := Over.pullback c)
    (pbNat a b c h).hom D.X
  exact Grp.mkIso' E

/-- Restrict the ORIGINAL cartesian group iso to the SAME generic base open. -/
def genericCoverGroupIso {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (G : Grp (Over U)) (D : Grp (Over S))
    (i : G ≅ (Over.pullback p).mapGrp.obj D) :
    (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback (p ∣_ V)).mapGrp.obj ((Over.pullback V.ι).mapGrp.obj D) :=
  (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.mapIso i ≪≫
    pbNatGroupIso (p ⁻¹ᵁ V).ι p ((p ⁻¹ᵁ V).ι ≫ p) rfl D ≪≫
    (pbNatGroupIso (p ∣_ V) V.ι ((p ⁻¹ᵁ V).ι ≫ p) (morphismRestrict_ι p V) D).symm

/-- The two actual generic projections still recover the ORIGINAL q.
    This is an equality of scheme morphisms on the whole generic model. -/
theorem genericCoverGroupIso_coordinate
    {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens) (G : Grp (Over U)) (D : Grp (Over S))
    (i : G ≅ (Over.pullback p).mapGrp.obj D) (q : G.X.left ⟶ D.X.left)
    (hi : i.hom.hom.hom.left ≫ pullback.fst D.X.hom p = q) :
    (genericCoverGroupIso p V G D i).hom.hom.hom.left ≫
        pullback.fst (pullback.snd D.X.hom V.ι) (p ∣_ V) ≫ pullback.fst D.X.hom V.ι =
      pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ q := by
  let a : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶
      pullback (pullback.snd D.X.hom p) (p ⁻¹ᵁ V).ι :=
    ((Over.pullback (p ⁻¹ᵁ V).ι).map i.hom.hom.hom).left
  let n₁ : pullback (pullback.snd D.X.hom p) (p ⁻¹ᵁ V).ι ⟶
      pullback D.X.hom ((p ⁻¹ᵁ V).ι ≫ p) :=
    (pbNatLeft (p ⁻¹ᵁ V).ι p ((p ⁻¹ᵁ V).ι ≫ p) rfl D.X).hom
  let n₂ : pullback D.X.hom ((p ⁻¹ᵁ V).ι ≫ p) ⟶
      pullback (pullback.snd D.X.hom V.ι) (p ∣_ V) :=
    (pbNatLeft (p ∣_ V) V.ι ((p ⁻¹ᵁ V).ι ≫ p) (morphismRestrict_ι p V) D.X).inv
  have h₂ : n₂ ≫ pullback.fst (pullback.snd D.X.hom V.ι) (p ∣_ V) ≫
      pullback.fst D.X.hom V.ι = pullback.fst D.X.hom ((p ⁻¹ᵁ V).ι ≫ p) :=
    pbNatLeft_inv_fst_fst _ _ _ _ _
  have h₁ : n₁ ≫ pullback.fst D.X.hom ((p ⁻¹ᵁ V).ι ≫ p) =
      pullback.fst (pullback.snd D.X.hom p) (p ⁻¹ᵁ V).ι ≫ pullback.fst D.X.hom p :=
    pbNatLeft_hom_fst _ _ _ _ _
  have ha : a ≫ pullback.fst (pullback.snd D.X.hom p) (p ⁻¹ᵁ V).ι =
      pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ i.hom.hom.hom.left := pullback.lift_fst _ _ _
  change a ≫ n₁ ≫ n₂ ≫ pullback.fst (pullback.snd D.X.hom V.ι) (p ∣_ V) ≫
      pullback.fst D.X.hom V.ι = _
  calc
    a ≫ n₁ ≫ n₂ ≫ pullback.fst (pullback.snd D.X.hom V.ι) (p ∣_ V) ≫ pullback.fst D.X.hom V.ι =
        a ≫ n₁ ≫ pullback.fst D.X.hom ((p ⁻¹ᵁ V).ι ≫ p) := by rw [h₂]
    _ = a ≫ pullback.fst (pullback.snd D.X.hom p) (p ⁻¹ᵁ V).ι ≫ pullback.fst D.X.hom p := by rw [h₁]
    _ = (pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ i.hom.hom.hom.left) ≫ pullback.fst D.X.hom p := by
      rw [← Category.assoc, ha]
      rfl
    _ = pullback.fst G.X.hom (p ⁻¹ᵁ V).ι ≫ q := by rw [Category.assoc, hi]

#print axioms pbNatGroupIso
#print axioms genericCoverGroupIso
#print axioms genericCoverGroupIso_coordinate

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
