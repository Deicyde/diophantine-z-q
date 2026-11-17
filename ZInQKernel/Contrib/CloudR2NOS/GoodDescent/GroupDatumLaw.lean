/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New group compatibility of the frozen, ACTUAL scheme descent datum.
Proof: identity on the open diagonal and the proved multiplicative generic
point equivalence; glue equalities of actual scheme morphisms. No desired
IsMonHom or group-compatible descent assumption is introduced.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GenericGroupLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupDatum
open GroupPoints

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
  (G : Grp (Over U)) (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)
  [Etale p] (c : S) [Mono (p.fiberToSpecResidueField c)]
  (hV : ∀ z : S, z ∉ V → z = c)

private theorem point_condition {T : Scheme.{u}} (u₁ u₂ : T ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (a : Over.mk u₁ ⟶ G.X) :
    (a.left ≫ G.X.hom) ≫ p = u₂ ≫ p := by
  have ha : a.left ≫ G.X.hom = u₁ := by simpa only [Over.mk_hom] using Over.w a
  exact (congrArg (· ≫ p) ha).trans h

private theorem transport_left {T : Scheme.{u}} (u₁ u₂ : T ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (a : Over.mk u₁ ⟶ G.X) :
    ((schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a).left =
      (genericModelOfGroupIso p V G A e).transportMap c hV a.left u₂
        (point_condition p G u₁ u₂ h a) := rfl

/-- On any equal-base test, the actual transported morphism is the original
    morphism, including the scheme/field maps. -/
theorem transport_on_equal {T T' : Scheme.{u}} (u₁ u₂ : T ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (a : Over.mk u₁ ⟶ G.X) (t : T' ⟶ T)
    (he : t ≫ u₁ = t ≫ u₂) :
    ((Over.homMk t : Over.mk (t ≫ u₂) ⟶ Over.mk u₂) ≫
      (schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a).left =
    ((Over.homMk t : Over.mk (t ≫ u₁) ⟶ Over.mk u₁) ≫ a).left := by
  change t ≫ ((schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a).left = t ≫ a.left
  rw [transport_left]
  apply (genericModelOfGroupIso p V G A e).transportMap_on_equal c hV a.left u₂ _ t
  have ha : a.left ≫ G.X.hom = u₁ := by simpa only [Over.mk_hom] using Over.w a
  simpa only [Category.assoc, ha] using he

/-- On any generic test, the actual transport equals the proven GROUP-point
    equivalence, not a substitute or an assumed map. -/
theorem transport_on_generic {T T' : Scheme.{u}} (u₁ u₂ : T ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (a : Over.mk u₁ ⟶ G.X) (t : T' ⟶ T)
    (h' : (t ≫ u₁) ≫ p = (t ≫ u₂) ≫ p)
    (hg : ∀ z : T', (t ≫ u₁) z ∈ p ⁻¹ᵁ V) :
    (Over.homMk t : Over.mk (t ≫ u₂) ⟶ Over.mk u₂) ≫
      (schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a =
    genericPoints p V G A e (t ≫ u₁) (t ≫ u₂) h' hg
      ((Over.homMk t : Over.mk (t ≫ u₁) ⟶ Over.mk u₁) ≫ a) := by
  let a' : Over.mk (t ≫ u₁) ⟶ G.X :=
    (Over.homMk t : Over.mk (t ≫ u₁) ⟶ Over.mk u₁) ≫ a
  have hga : ∀ z : T', (t ≫ a.left) z ∈ G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V) :=
    point_is_generic p V G (t ≫ u₁) hg a'
  have hpa : ((t ≫ a.left) ≫ G.X.hom) ≫ p = (t ≫ u₂) ≫ p :=
    point_condition p G (t ≫ u₁) (t ≫ u₂) h' a'
  apply Over.OverMorphism.ext
  change t ≫ ((schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a).left =
    (genericPoints p V G A e (t ≫ u₁) (t ≫ u₂) h' hg a').left
  rw [transport_left,
    (genericModelOfGroupIso p V G A e).transportMap_on_generic c hV a.left u₂ _ t hga hpa]
  exact genericMap_eq_genericPoints p V G A e (t ≫ u₁) (t ≫ u₂) h' hg a'

private theorem mul_left_congr {T : Scheme.{u}} {u₁ u₂ : T ⟶ U} (he : u₁ = u₂)
    (a₁ b₁ : Over.mk u₁ ⟶ G.X) (a₂ b₂ : Over.mk u₂ ⟶ G.X)
    (ha : a₁.left = a₂.left) (hb : b₁.left = b₂.left) :
    (a₁ * b₁).left = (a₂ * b₂).left := by
  subst u₂
  have ha' : a₁ = a₂ := Over.OverMorphism.ext ha
  have hb' : b₁ = b₂ := Over.OverMorphism.ext hb
  rw [ha', hb']

/-- Multiplication compatibility of the ACTUAL globally constructed scheme
    datum. The diagonal/generic cover proves this, not a supplied hdesc or
    IsMonHom assumption. -/
theorem transport_mul {T : Scheme.{u}} (u₁ u₂ : T ⟶ U)
    (h : u₁ ≫ p = u₂ ≫ p) (a b : Over.mk u₁ ⟶ G.X) :
    (schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h (a * b) =
      (schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h a *
        (schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h b := by
  let d := schemeDatumOfGroupIso p V G A e c hV
  let ta := d.transport u₁ u₂ h a
  let tb := d.transport u₁ u₂ h b
  let tab := d.transport u₁ u₂ h (a * b)
  let D := equalityOpen p u₁ u₂ h
  let H := (u₁ ≫ p) ⁻¹ᵁ V
  apply Over.OverMorphism.ext
  apply hom_ext_two (equality_sup_generic_eq_top p c V hV u₁ u₂ h)
  · let t₁ : Over.mk (D.ι ≫ u₁) ⟶ Over.mk u₁ := Over.homMk D.ι
    let t₂ : Over.mk (D.ι ≫ u₂) ⟶ Over.mk u₂ := Over.homMk D.ι
    have he : D.ι ≫ u₁ = D.ι ≫ u₂ := equalityOpen_eq p u₁ u₂ h
    have ha : (t₂ ≫ ta).left = (t₁ ≫ a).left := transport_on_equal p V G A e c hV u₁ u₂ h a D.ι he
    have hb : (t₂ ≫ tb).left = (t₁ ≫ b).left := transport_on_equal p V G A e c hV u₁ u₂ h b D.ι he
    have hab : (t₂ ≫ tab).left = (t₁ ≫ (a * b)).left :=
      transport_on_equal p V G A e c hV u₁ u₂ h (a * b) D.ι he
    change D.ι ≫ tab.left = D.ι ≫ (ta * tb).left
    calc
      D.ι ≫ tab.left = (t₁ ≫ (a * b)).left := hab
      _ = ((t₁ ≫ a) * (t₁ ≫ b)).left := by rw [MonObj.comp_mul]
      _ = ((t₂ ≫ ta) * (t₂ ≫ tb)).left := mul_left_congr G he _ _ _ _ ha.symm hb.symm
      _ = (t₂ ≫ (ta * tb)).left := by rw [MonObj.comp_mul]
      _ = D.ι ≫ (ta * tb).left := rfl
  · let t₁ : Over.mk (H.ι ≫ u₁) ⟶ Over.mk u₁ := Over.homMk H.ι
    let t₂ : Over.mk (H.ι ≫ u₂) ⟶ Over.mk u₂ := Over.homMk H.ι
    have h' : (H.ι ≫ u₁) ≫ p = (H.ι ≫ u₂) ≫ p := by
      simpa only [Category.assoc] using congrArg (H.ι ≫ ·) h
    have hg : ∀ z : H.toScheme, (H.ι ≫ u₁) z ∈ p ⁻¹ᵁ V := by
      intro z
      change p (u₁ z.1) ∈ V
      exact z.2
    let F := genericPoints p V G A e (H.ι ≫ u₁) (H.ι ≫ u₂) h' hg
    have ha : t₂ ≫ ta = F (t₁ ≫ a) := transport_on_generic p V G A e c hV u₁ u₂ h a H.ι h' hg
    have hb : t₂ ≫ tb = F (t₁ ≫ b) := transport_on_generic p V G A e c hV u₁ u₂ h b H.ι h' hg
    have hab : t₂ ≫ tab = F (t₁ ≫ (a * b)) :=
      transport_on_generic p V G A e c hV u₁ u₂ h (a * b) H.ι h' hg
    change H.ι ≫ tab.left = H.ι ≫ (ta * tb).left
    have he : t₂ ≫ tab = t₂ ≫ (ta * tb) := by
      rw [hab, MonObj.comp_mul, map_mul, ← ha, ← hb, MonObj.comp_mul]
    exact congrArg Over.Hom.left he

/-- The actual point transport is a group homomorphism. Unit/inverse
    compatibility follows from the proved multiplication compatibility. -/
def transportHom {T : Scheme.{u}} (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p) :
    (Over.mk u₁ ⟶ G.X) →* (Over.mk u₂ ⟶ G.X) :=
  MonoidHom.mk' ((schemeDatumOfGroupIso p V G A e c hV).transport u₁ u₂ h)
    (transport_mul p V G A e c hV u₁ u₂ h)

#print axioms transport_mul
#print axioms transportHom

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupDatum
