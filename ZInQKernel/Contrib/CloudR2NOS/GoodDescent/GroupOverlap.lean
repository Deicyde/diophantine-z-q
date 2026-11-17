/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New IsMonHom and GROUP-object overlap isomorphism for the actual, frozen
scheme comparison maps. No IsMonHom, group-datum, effectiveness or model
properness assumption is supplied. All group compatibility is proved from
the given generic group iso and the diagonal/generic cover.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupDatumLaw
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.OverlapIso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupDatum
open GroupPoints

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
  (G : Grp (Over U)) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)
  [Etale p] (c : S) [Mono (p.fiberToSpecResidueField c)]
  (hV : ∀ z : S, z ∉ V → z = c)

/-- The exact, already constructed SCHEME overlap iso, on the underlying
    objects of the two base-changed groups. -/
def overlapSchemeIso {R : Scheme.{u}} (u₁ u₂ : R ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) :
    ((Over.pullback u₁).mapGrp.obj G).X ≅ ((Over.pullback u₂).mapGrp.obj G).X :=
  (genericModelOfGroupIso p V G A e).overlapIso c hV u₁ u₂ h

private theorem test_condition {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (T : Over R) :
    (T.hom ≫ u₁) ≫ p = (T.hom ≫ u₂) ≫ p := by
  simpa only [Category.assoc] using congrArg (T.hom ≫ ·) h

/-- A genuinely constructed homomorphism on every test scheme's group of
    points: pull back, transport by the proven group datum, and pull back
    again. The underlying scheme map is identified below. -/
def overlapPointHom {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (T : Over R) :
    (T ⟶ ((Over.pullback u₁).mapGrp.obj G).X) →*
      (T ⟶ ((Over.pullback u₂).mapGrp.obj G).X) :=
  (pullbackPts u₂ T G).toMonoidHom.comp
    ((transportHom p V G A e c hV (T.hom ≫ u₁) (T.hom ≫ u₂) (test_condition p u₁ u₂ h T)).comp
      (pullbackPts u₁ T G).symm.toMonoidHom)

private theorem transport_congr {T : Scheme.{u}} {x x' : T ⟶ G.X.left} {v v' : T ⟶ U}
    (hx : x = x') (hv : v = v')
    (h : (x ≫ G.X.hom) ≫ p = v ≫ p) (h' : (x' ≫ G.X.hom) ≫ p = v' ≫ p) :
    (genericModelOfGroupIso p V G A e).transportMap c hV x v h =
      (genericModelOfGroupIso p V G A e).transportMap c hV x' v' h' := by
  cases hx
  cases hv
  rfl

/-- The constructed homomorphism on points is EXACTLY postcomposition
    with the original scheme overlap morphism, not a replacement map. -/
theorem overlapPointHom_eq_postcomp {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (T : Over R)
    (a : T ⟶ ((Over.pullback u₁).mapGrp.obj G).X) :
    overlapPointHom p V G A e c hV u₁ u₂ h T a =
      a ≫ (overlapSchemeIso p V G A e c hV u₁ u₂ h).hom := by
  let M := genericModelOfGroupIso p V G A e
  let a₁ := pullback.fst G.X.hom u₁
  let b₁ := pullback.snd G.X.hom u₁
  let ar : T.left ⟶ pullback G.X.hom u₁ := a.left
  let b : (Over.map u₁).obj T ⟶ G.X := (pullbackPts u₁ T G).symm a
  let th := test_condition p u₁ u₂ h T
  let d : Over.mk (T.hom ≫ u₂) ⟶ G.X :=
    (schemeDatumOfGroupIso p V G A e c hV).transport (T.hom ≫ u₁) (T.hom ≫ u₂) th b
  let yr : T.left ⟶ pullback G.X.hom u₂ := (overlapPointHom p V G A e c hV u₁ u₂ h T a).left
  let zr : T.left ⟶ pullback G.X.hom u₂ := (pullbackPts u₂ T G d).left
  let er : pullback G.X.hom u₁ ⟶ pullback G.X.hom u₂ :=
    (overlapSchemeIso p V G A e c hV u₁ u₂ h).hom.left
  have hpoint : overlapPointHom p V G A e c hV u₁ u₂ h T a = pullbackPts u₂ T G d := rfl
  have hyz : yr = zr := congrArg Over.Hom.left hpoint
  have hz₁ : zr ≫ pullback.fst G.X.hom u₂ = d.left := pullbackPts_fst _ _ _ _
  have hz₂ : zr ≫ pullback.snd G.X.hom u₂ = T.hom := pullbackPts_snd _ _ _ _
  have hb : b.left = ar ≫ a₁ := pullbackPts_symm_left _ _ _ _
  have hab : ar ≫ b₁ = T.hom := by
    have ha := Over.w a
    change ar ≫ b₁ = T.hom at ha
    exact ha
  have hcomp : (a₁ ≫ G.X.hom) ≫ p = (b₁ ≫ u₂) ≫ p := by
    rw [pullback.condition, Category.assoc, Category.assoc, h]
  have hv : ar ≫ (b₁ ≫ u₂) = T.hom ≫ u₂ := by rw [← Category.assoc, hab]
  have h' : ((ar ≫ a₁) ≫ G.X.hom) ≫ p = (ar ≫ (b₁ ≫ u₂)) ≫ p := by
    simpa only [Category.assoc] using congrArg (fun x : pullback G.X.hom u₁ ⟶ S => ar ≫ x) hcomp
  have h'' : ((ar ≫ a₁) ≫ G.X.hom) ≫ p = (T.hom ≫ u₂) ≫ p := by rw [← hv]; exact h'
  have hbbase : b.left ≫ G.X.hom = T.hom ≫ u₁ := by
    have hw := Over.w b
    change b.left ≫ G.X.hom = T.hom ≫ u₁ at hw
    exact hw
  let hout : (b.left ≫ G.X.hom) ≫ p = (T.hom ≫ u₂) ≫ p := (congrArg (· ≫ p) hbbase).trans th
  have hd : d.left = M.transportMap c hV b.left (T.hom ≫ u₂) hout := rfl
  have hn := M.transportMap_natural c hV a₁ (b₁ ≫ u₂) hcomp ar h'
  have he : d.left = ar ≫ M.transportMap c hV a₁ (b₁ ≫ u₂) hcomp :=
    hd.trans ((transport_congr p V G A e c hV hb rfl hout h'').trans
      ((transport_congr p V G A e c hV rfl hv.symm h'' h').trans hn))
  have her₁ : er ≫ pullback.fst G.X.hom u₂ =
      M.transportMap c hV a₁ (b₁ ≫ u₂) hcomp := M.comparisonMap_fst c hV u₁ u₂ h
  have her₂ : er ≫ pullback.snd G.X.hom u₂ = b₁ := M.comparisonMap_snd c hV u₁ u₂ h
  have hraw : yr = ar ≫ er := by
    apply pullback.hom_ext
    · calc
        yr ≫ pullback.fst G.X.hom u₂ = d.left := (congrArg (· ≫ pullback.fst G.X.hom u₂) hyz).trans hz₁
        _ = ar ≫ M.transportMap c hV a₁ (b₁ ≫ u₂) hcomp := he
        _ = (ar ≫ er) ≫ pullback.fst G.X.hom u₂ := by rw [Category.assoc, her₁]
    · calc
        yr ≫ pullback.snd G.X.hom u₂ = T.hom := (congrArg (· ≫ pullback.snd G.X.hom u₂) hyz).trans hz₂
        _ = ar ≫ b₁ := hab.symm
        _ = (ar ≫ er) ≫ pullback.snd G.X.hom u₂ := by rw [Category.assoc, her₂]
  apply Over.OverMorphism.ext
  exact hraw

/-- Actual IsMonHom of the original overlap morphism. The pointwise group
    homomorphism above proves the unit and multiplication diagrams on their
    universal test schemes. -/
theorem overlapSchemeIso_isMonHom {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    IsMonHom (overlapSchemeIso p V G A e c hV u₁ u₂ h).hom := by
  let G₁ := ((Over.pullback u₁).mapGrp.obj G).X
  let G₂ := ((Over.pullback u₂).mapGrp.obj G).X
  let f := (overlapSchemeIso p V G A e c hV u₁ u₂ h).hom
  have hm (T : Over R) (a b : T ⟶ G₁) : (a * b) ≫ f = a ≫ f * b ≫ f := by
    rw [← overlapPointHom_eq_postcomp, ← overlapPointHom_eq_postcomp,
      ← overlapPointHom_eq_postcomp]
    exact map_mul (overlapPointHom p V G A e c hV u₁ u₂ h T) a b
  have ho (T : Over R) : (1 : T ⟶ G₁) ≫ f = 1 := by
    rw [← overlapPointHom_eq_postcomp]
    exact map_one (overlapPointHom p V G A e c hV u₁ u₂ h T)
  refine ⟨?_, ?_⟩
  · change η[G₁] ≫ f = η[G₂]
    rw [MonObj.one_eq_one, MonObj.one_eq_one, ho]
  · change μ[G₁] ≫ f = (f ⊗ₘ f) ≫ μ[G₂]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hm, MonObj.comp_mul]
    exact congrArg₂ (fun x y : G₁ ⊗ G₁ ⟶ G₂ => x * y)
      (tensorHom_fst f f).symm (tensorHom_snd f f).symm

/-- Upgrade the SAME original scheme comparison to an actual isomorphism
    of group objects, with no extra compatibility hypothesis. -/
def overlapGroupIso {R : Scheme.{u}} (u₁ u₂ : R ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) :
    (Over.pullback u₁).mapGrp.obj G ≅ (Over.pullback u₂).mapGrp.obj G := by
  haveI := overlapSchemeIso_isMonHom p V G A e c hV u₁ u₂ h
  exact Grp.mkIso' (overlapSchemeIso p V G A e c hV u₁ u₂ h)

/-- The actual GROUP overlap maps satisfy the already proved universal
    triple-overlap cocycle, with every underlying scheme map unchanged. -/
theorem overlapGroupIso_cocycle {R : Scheme.{u}} (u₁ u₂ u₃ : R ⟶ U)
    (h₁₂ : u₁ ≫ p = u₂ ≫ p) (h₂₃ : u₂ ≫ p = u₃ ≫ p) :
    (overlapGroupIso p V G A e c hV u₁ u₂ h₁₂).hom ≫
        (overlapGroupIso p V G A e c hV u₂ u₃ h₂₃).hom =
      (overlapGroupIso p V G A e c hV u₁ u₃ (h₁₂.trans h₂₃)).hom := by
  apply (Grp.forget (Over R)).map_injective
  apply Over.OverMorphism.ext
  exact (genericModelOfGroupIso p V G A e).comparisonMap_comp c hV u₁ u₂ u₃ h₁₂ h₂₃

#print axioms overlapPointHom_eq_postcomp
#print axioms overlapSchemeIso_isMonHom
#print axioms overlapGroupIso
#print axioms overlapGroupIso_cocycle

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupDatum
