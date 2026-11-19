/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New multiplication/unit compatibility on generic test schemes, retaining
actual base morphisms and the given generic group-object isomorphism.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupGenericCompatibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints

private theorem base_mem_other {U S T : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (hg : ∀ z : T, u₁ z ∈ p ⁻¹ᵁ V) : ∀ z : T, u₂ z ∈ p ⁻¹ᵁ V := by
  intro z
  have hz := congrArg (fun q : T ⟶ S => q z) h
  simp only [Scheme.Hom.comp_apply] at hz
  change p (u₂ z) ∈ V
  rw [← hz]
  exact hg z

private theorem lifted_base_condition {U S T : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (hg : ∀ z : T, u₁ z ∈ p ⁻¹ᵁ V) :
    intoOpen u₁ (p ⁻¹ᵁ V) hg ≫ (p ∣_ V) =
      intoOpen u₂ (p ⁻¹ᵁ V) (base_mem_other p V u₁ u₂ h hg) ≫ (p ∣_ V) := by
  apply (cancel_mono V.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, intoOpen_ι_assoc]
  exact h

/-- Point genericity is derived from its literal original base map. -/
theorem point_is_generic {U S T : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (G : Grp (Over U)) (u : T ⟶ U) (hg : ∀ z : T, u z ∈ p ⁻¹ᵁ V)
    (a : Over.mk u ⟶ G.X) : ∀ z : T, a.left z ∈ G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  intro z
  have hz := congrArg (fun q : T ⟶ U => q z) (Over.w a)
  simp only [Scheme.Hom.comp_apply, Over.mk_hom] at hz
  change G.X.hom (a.left z) ∈ p ⁻¹ᵁ V
  rw [hz]
  exact hg z

private theorem point_base_condition {U S T : Scheme.{u}} (p : U ⟶ S)
    (G : Grp (Over U)) (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (a : Over.mk u₁ ⟶ G.X) : (a.left ≫ G.X.hom) ≫ p = u₂ ≫ p := by
  have ha : a.left ≫ G.X.hom = u₁ := by simpa only [Over.mk_hom] using Over.w a
  exact (congrArg (· ≫ p) ha).trans h

private theorem genericMap_congr {X U S T : Scheme.{u}} {f : X ⟶ U} {p : U ⟶ S} {V : S.Opens}
    (M : GenericModel f p V) {x x' : T ⟶ X} {v v' : T ⟶ U}
    (he : x = x') (hv : v = v')
    (h : (x ≫ f) ≫ p = v ≫ p) (h' : (x' ≫ f) ≫ p = v' ≫ p)
    (hg : ∀ z : T, x z ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V))
    (hg' : ∀ z : T, x' z ∈ f ⁻¹ᵁ (p ⁻¹ᵁ V)) :
    M.genericMap x v h hg = M.genericMap x' v' h' hg' := by
  cases he
  cases hv
  rfl

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (G : Grp (Over U)) (A : Grp (Over V.toScheme))
    (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- Actual multiplicative point transport for any wholly generic test.
    The casts are literal identity changes of base and preserve all fields. -/
def genericPoints {T : Scheme.{u}} (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (hg : ∀ z : T, u₁ z ∈ p ⁻¹ᵁ V) : (Over.mk u₁ ⟶ G.X) ≃* (Over.mk u₂ ⟶ G.X) :=
  let a₁ := intoOpen u₁ (p ⁻¹ᵁ V) hg
  let a₂ := intoOpen u₂ (p ⁻¹ᵁ V) (base_mem_other p V u₁ u₂ h hg)
  let ha := lifted_base_condition p V u₁ u₂ h hg
  let c₁ : (Over.mk u₁ ⟶ G.X) ≃* ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk a₁) ⟶ G.X) :=
    pointCongr G (intoOpen_ι u₁ (p ⁻¹ᵁ V) hg).symm
  let c₂ : ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk a₂) ⟶ G.X) ≃* (Over.mk u₂ ⟶ G.X) :=
    pointCongr G (intoOpen_ι u₂ (p ⁻¹ᵁ V) (base_mem_other p V u₁ u₂ h hg))
  (c₁.trans (genericPointEquiv p V G A e a₁ a₂ ha)).trans c₂

/-- Identification with the already CONSTRUCTED scheme transport. -/
theorem genericMap_eq_genericPoints {T : Scheme.{u}} (u₁ u₂ : T ⟶ U) (h : u₁ ≫ p = u₂ ≫ p)
    (hg : ∀ z : T, u₁ z ∈ p ⁻¹ᵁ V) (a : Over.mk u₁ ⟶ G.X) :
    (genericModelOfGroupIso p V G A e).genericMap a.left u₂
      (point_base_condition p G u₁ u₂ h a) (point_is_generic p V G u₁ hg a) =
      (genericPoints p V G A e u₁ u₂ h hg a).left := by
  let a₁ := intoOpen u₁ (p ⁻¹ᵁ V) hg
  let a₂ := intoOpen u₂ (p ⁻¹ᵁ V) (base_mem_other p V u₁ u₂ h hg)
  let ha := lifted_base_condition p V u₁ u₂ h hg
  let c₁ : (Over.mk u₁ ⟶ G.X) ≃* ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk a₁) ⟶ G.X) :=
    pointCongr G (intoOpen_ι u₁ (p ⁻¹ᵁ V) hg).symm
  let c₂ : ((Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk a₂) ⟶ G.X) ≃* (Over.mk u₂ ⟶ G.X) :=
    pointCongr G (intoOpen_ι u₂ (p ⁻¹ᵁ V) (base_mem_other p V u₁ u₂ h hg))
  have hc₁ : (c₁ a).left = a.left := pointCongr_left _ _ _
  have ha₂ : a₂ ≫ (p ⁻¹ᵁ V).ι = u₂ := intoOpen_ι _ _ _
  have he := genericMap_eq_genericPointEquiv p V G A e a₁ a₂ ha (c₁ a)
  have hcmp := genericMap_congr (genericModelOfGroupIso p V G A e) hc₁ ha₂
    (genericPoint_base_condition p V G a₁ a₂ ha (c₁ a))
    (point_base_condition p G u₁ u₂ h a)
    (point_mem_generic p V G a₁ (c₁ a)) (point_is_generic p V G u₁ hg a)
  have hc₂ : (c₂ (genericPointEquiv p V G A e a₁ a₂ ha (c₁ a))).left =
      (genericPointEquiv p V G A e a₁ a₂ ha (c₁ a)).left := pointCongr_left _ _ _
  change (genericModelOfGroupIso p V G A e).genericMap a.left u₂ _ _ =
    (c₂ (genericPointEquiv p V G A e a₁ a₂ ha (c₁ a))).left
  exact hcmp.symm.trans (he.trans hc₂.symm)

#print axioms genericPoints
#print axioms genericMap_eq_genericPoints

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints
