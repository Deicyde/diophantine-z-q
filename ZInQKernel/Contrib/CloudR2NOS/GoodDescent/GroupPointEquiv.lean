/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New native categorical group-point transport after the frozen checkpoint.
Transport is conjugation by the GIVEN generic GROUP-object isomorphism,
with the canonical pullback point equivalences and a literal identity
change of base. Every factor is an actual multiplicative equivalence.
No IsMonHom/overlap-compatibility hypothesis is supplied for the result.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints

/-- The pullback adjunction is an actual equivalence of groups of points. -/
def pullbackPts {B S : Scheme.{u}} (f : B ⟶ S) (T : Over B) (G : Grp (Over S)) :
    ((Over.map f).obj T ⟶ G.X) ≃* (T ⟶ ((Over.pullback f).mapGrp.obj G).X) :=
  letI : GrpObj ((Over.pullback f).obj G.X) := Functor.grpObjObj
  { toEquiv := (Over.mapPullbackAdj f).homEquiv T G.X
    map_mul' := by
      intro a b
      change (Over.mapPullbackAdj f).homEquiv T G.X (a * b) =
        (Over.mapPullbackAdj f).homEquiv T G.X a * (Over.mapPullbackAdj f).homEquiv T G.X b
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
        Functor.map_mul, MonObj.comp_mul] }

@[simp]
theorem pullbackPts_symm_left {B S : Scheme.{u}} (f : B ⟶ S) (T : Over B) (G : Grp (Over S))
    (a : T ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    ((pullbackPts f T G).symm a).left = a.left ≫ pullback.fst G.X.hom f := rfl

@[simp]
theorem pullbackPts_fst {B S : Scheme.{u}} (f : B ⟶ S) (T : Over B) (G : Grp (Over S))
    (a : (Over.map f).obj T ⟶ G.X) :
    (pullbackPts f T G a).left ≫ pullback.fst G.X.hom f = a.left := by
  have h := congrArg Over.Hom.left ((pullbackPts f T G).symm_apply_apply a)
  simpa only [pullbackPts_symm_left] using h

@[simp]
theorem pullbackPts_snd {B S : Scheme.{u}} (f : B ⟶ S) (T : Over B) (G : Grp (Over S))
    (a : (Over.map f).obj T ⟶ G.X) :
    (pullbackPts f T G a).left ≫ pullback.snd G.X.hom f = T.hom := by
  have h := Over.w (pullbackPts f T G a)
  change (pullbackPts f T G a).left ≫ pullback.snd G.X.hom f = T.hom at h
  exact h

/-- Postcomposition by an actual group-object isomorphism. -/
def postPts {S : Scheme.{u}} {G H : Grp (Over S)} (e : G ≅ H) (T : Over S) :
    (T ⟶ G.X) ≃* (T ⟶ H.X) :=
  let E : G.X ≅ H.X := (Grp.forget _).mapIso e
  haveI : IsMonHom E.hom := inferInstanceAs (IsMonHom e.hom.hom.hom)
  { toFun a := a ≫ E.hom
    invFun a := a ≫ E.inv
    left_inv a := by simp
    right_inv a := by simp
    map_mul' a b := MonObj.mul_comp a b E.hom }

/-- Precomposition by an isomorphism of the TEST scheme also preserves
    its group of points. There is no group-object assumption on the test. -/
def prePts {S : Scheme.{u}} {T₁ T₂ : Over S} (e : T₂ ≅ T₁) (G : Grp (Over S)) :
    (T₁ ⟶ G.X) ≃* (T₂ ⟶ G.X) where
  toFun a := e.hom ≫ a
  invFun a := e.inv ≫ a
  left_inv a := by simp
  right_inv a := by simp
  map_mul' a b := MonObj.comp_mul e.hom a b

@[simp]
theorem prePts_left {S : Scheme.{u}} {T₁ T₂ : Over S} (e : T₂ ≅ T₁)
    (G : Grp (Over S)) (a : T₁ ⟶ G.X) :
    (prePts e G a).left = e.hom.left ≫ a.left := rfl

/-- A literal identity map of the scheme T changes the base equality;
    its underlying scheme-point morphism stays unchanged. -/
def pointCongr {S T : Scheme.{u}} (G : Grp (Over S)) {t₁ t₂ : T ⟶ S} (h : t₁ = t₂) :
    (Over.mk t₁ ⟶ G.X) ≃* (Over.mk t₂ ⟶ G.X) := by
  subst t₂
  exact MulEquiv.refl _

@[simp]
theorem pointCongr_left {S T : Scheme.{u}} (G : Grp (Over S)) {t₁ t₂ : T ⟶ S}
    (h : t₁ = t₂) (a : Over.mk t₁ ⟶ G.X) : (pointCongr G h a).left = a.left := by
  subst t₂
  rfl

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
  (G : Grp (Over U)) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- Actual multiplicative generic transport on points with specified maps
    to the generic open of U. Its middle base change is the IDENTITY on T. -/
def genericPointEquiv {T : Scheme.{u}}
    (u₁ u₂ : T ⟶ (p ⁻¹ᵁ V).toScheme) (h : u₁ ≫ (p ∣_ V) = u₂ ≫ (p ∣_ V)) :
    ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk u₁) ⟶ G.X) ≃*
      ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk u₂) ⟶ G.X) :=
  let E : (Over.map (p ∣_ V)).obj (Over.mk u₂) ≅ (Over.map (p ∣_ V)).obj (Over.mk u₁) :=
    Over.isoMk (Iso.refl T) (by
      change (𝟙 T) ≫ (u₁ ≫ (p ∣_ V)) = u₂ ≫ (p ∣_ V)
      exact (Category.id_comp _).trans h)
  ((((((pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₁) G).trans (postPts e (Over.mk u₁))).trans
      ((pullbackPts (p ∣_ V) (Over.mk u₁) A).symm)).trans (prePts E A)).trans
      (pullbackPts (p ∣_ V) (Over.mk u₂) A)).trans ((postPts e (Over.mk u₂)).symm)).trans
      ((pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₂) G).symm)

/-- The transport retains the ACTUAL coordinates in the original generic
    group A, not merely the topological image of a geometric point. -/
theorem genericPointEquiv_coordinate {T : Scheme.{u}}
    (u₁ u₂ : T ⟶ (p ⁻¹ᵁ V).toScheme) (h : u₁ ≫ (p ∣_ V) = u₂ ≫ (p ∣_ V))
    (a : (Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk u₁) ⟶ G.X) :
    ((pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₂) G
      (genericPointEquiv p V G A e u₁ u₂ h a)) ≫ ((Grp.forget _).mapIso e).hom).left ≫
        pullback.fst A.X.hom (p ∣_ V) =
    ((pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₁) G a) ≫ ((Grp.forget _).mapIso e).hom).left ≫
        pullback.fst A.X.hom (p ∣_ V) := by
  change ((pullbackPts (p ∣_ V) (Over.mk u₂) A).symm
      (postPts e (Over.mk u₂) (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₂) G
        (genericPointEquiv p V G A e u₁ u₂ h a)))).left =
    ((pullbackPts (p ∣_ V) (Over.mk u₁) A).symm
      (postPts e (Over.mk u₁) (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₁) G a))).left
  simp only [genericPointEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_apply]
  simp only [prePts_left, Over.isoMk_hom_left, Iso.refl_hom]
  let q : T ⟶ A.X.left := ((pullbackPts (p ∣_ V) (Over.mk u₁) A).symm
    (postPts e (Over.mk u₁) (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₁) G a))).left
  change (𝟙 T) ≫ q = q
  exact Category.id_comp q

#print axioms pullbackPts
#print axioms genericPointEquiv
#print axioms genericPointEquiv_coordinate

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints
