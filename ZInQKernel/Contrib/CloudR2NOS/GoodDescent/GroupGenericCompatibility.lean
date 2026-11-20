/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New proof identifying the ACTUAL generic scheme transport with the native
multiplicative point equivalence of the given generic group-object iso.
No compatibility of the resulting map is added as an assumption.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupPointEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens) (G : Grp (Over U))

/-- Genericity follows from the ACTUAL base map of the point. -/
theorem point_mem_generic {T : Scheme.{u}} (t : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (a : (Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk t) ⟶ G.X) :
    ∀ z : T, a.left z ∈ G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  have ha : a.left ≫ G.X.hom = t ≫ (p ⁻¹ᵁ V).ι := by
    simpa only [Over.map_obj_hom, Over.mk_hom] using Over.w a
  intro z
  change G.X.hom (a.left z) ∈ p ⁻¹ᵁ V
  have hz := congrArg (fun q : T ⟶ U => q z) ha
  simp only [Scheme.Hom.comp_apply] at hz
  rw [hz]
  exact (t z).2

/-- The opened point is the canonical group-object pullback point. -/
theorem openPoint_to_pullback {T : Scheme.{u}} (t : T ⟶ (p ⁻¹ᵁ V).toScheme)
    (a : (Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk t) ⟶ G.X) :
    intoOpen a.left (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) (point_mem_generic p V G t a) ≫
        (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv =
      (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk t) G a).left := by
  let l : T ⟶ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme :=
    intoOpen a.left (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) (point_mem_generic p V G t a)
  let r : T ⟶ pullback G.X.hom (p ⁻¹ᵁ V).ι := (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk t) G a).left
  have hl : l ≫ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι = a.left := intoOpen_ι _ _ _
  have hr₁ : r ≫ pullback.fst G.X.hom (p ⁻¹ᵁ V).ι = a.left := pullbackPts_fst _ _ _ _
  have hr₂ : r ≫ pullback.snd G.X.hom (p ⁻¹ᵁ V).ι = t := pullbackPts_snd _ _ _ _
  change l ≫ (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv = r
  apply pullback.hom_ext
  · rw [hr₁, Category.assoc, pullbackRestrictIsoRestrict_inv_fst]
    exact hl
  · rw [hr₂]
    change l ≫ (G.X.hom ∣_ (p ⁻¹ᵁ V)) = t
    apply (cancel_mono (p ⁻¹ᵁ V).ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl]
    simpa only [Over.map_obj_hom, Over.mk_hom] using Over.w a

variable (A : Grp (Over V.toScheme))
  (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- Equality of the original-base composites is forced by the generic base
    equality and the point's literal structure morphism. -/
theorem genericPoint_base_condition {T : Scheme.{u}}
    (u₁ u₂ : T ⟶ (p ⁻¹ᵁ V).toScheme) (h : u₁ ≫ (p ∣_ V) = u₂ ≫ (p ∣_ V))
    (a : (Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk u₁) ⟶ G.X) :
    (a.left ≫ G.X.hom) ≫ p = (u₂ ≫ (p ⁻¹ᵁ V).ι) ≫ p := by
  have ha : a.left ≫ G.X.hom = u₁ ≫ (p ⁻¹ᵁ V).ι := by
    simpa only [Over.map_obj_hom, Over.mk_hom] using Over.w a
  rw [ha, Category.assoc, ← morphismRestrict_ι p V, ← Category.assoc, h,
    Category.assoc, morphismRestrict_ι, ← Category.assoc]

/-- The already constructed generic scheme morphism is LITERALLY the point
    transport by the given group-object iso. In particular it preserves
    multiplication and the unit without an assumed IsMonHom input. -/
theorem genericMap_eq_genericPointEquiv {T : Scheme.{u}}
    (u₁ u₂ : T ⟶ (p ⁻¹ᵁ V).toScheme) (h : u₁ ≫ (p ∣_ V) = u₂ ≫ (p ∣_ V))
    (a : (Over.map (p ⁻¹ᵁ V).ι).obj (Over.mk u₁) ⟶ G.X) :
    (genericModelOfGroupIso p V G A e).genericMap a.left (u₂ ≫ (p ⁻¹ᵁ V).ι)
      (genericPoint_base_condition p V G u₁ u₂ h a) (point_mem_generic p V G u₁ a) =
      (genericPointEquiv p V G A e u₁ u₂ h a).left := by
  let M := genericModelOfGroupIso p V G A e
  let b := genericPointEquiv p V G A e u₁ u₂ h a
  let a₀ : T ⟶ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme :=
    intoOpen a.left (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) (point_mem_generic p V G u₁ a)
  let b₀ : T ⟶ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme :=
    intoOpen b.left (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) (point_mem_generic p V G u₂ b)
  let E : ((Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G).X ≅
      ((Over.pullback (p ∣_ V)).mapGrp.obj A).X := (Grp.forget _).mapIso e
  let r : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶ pullback A.X.hom (p ∣_ V) := E.hom.left
  let pa : T ⟶ pullback G.X.hom (p ⁻¹ᵁ V).ι := (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₁) G a).left
  let pb : T ⟶ pullback G.X.hom (p ⁻¹ᵁ V).ι := (pullbackPts (p ⁻¹ᵁ V).ι (Over.mk u₂) G b).left
  let qA := pullback.fst A.X.hom (p ∣_ V)
  have ha₀ : a₀ ≫ (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv = pa :=
    openPoint_to_pullback p V G u₁ a
  have hb₀ : b₀ ≫ (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv = pb :=
    openPoint_to_pullback p V G u₂ b
  have hcoord : (pb ≫ r) ≫ qA = (pa ≫ r) ≫ qA :=
    genericPointEquiv_coordinate p V G A e u₁ u₂ h a
  have hMq : M.q = ((pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv ≫ r) ≫ qA := rfl
  have hqa : a₀ ≫ M.q = (pa ≫ r) ≫ qA := by
    change ((a₀ ≫ (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv) ≫ r) ≫ qA =
      (pa ≫ r) ≫ qA
    exact congrArg (fun z : T ⟶ pullback G.X.hom (p ⁻¹ᵁ V).ι => (z ≫ r) ≫ qA) ha₀
  have hqb : b₀ ≫ M.q = (pb ≫ r) ≫ qA := by
    change ((b₀ ≫ (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv) ≫ r) ≫ qA =
      (pb ≫ r) ≫ qA
    exact congrArg (fun z : T ⟶ pullback G.X.hom (p ⁻¹ᵁ V).ι => (z ≫ r) ≫ qA) hb₀
  have hq : b₀ ≫ M.q = a₀ ≫ M.q := hqb.trans (hcoord.trans hqa.symm)
  let y : T ⟶ G.X.left := M.genericMap a.left (u₂ ≫ (p ⁻¹ᵁ V).ι)
    (genericPoint_base_condition p V G u₁ u₂ h a) (point_mem_generic p V G u₁ a)
  have hy : ∀ z : T, y z ∈ G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V) := M.genericMap_mem _ _ _ _
  let y₀ : T ⟶ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme := intoOpen y (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)) hy
  have hyι : y₀ ≫ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι = y := intoOpen_ι _ _ _
  have hbι : b₀ ≫ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι = b.left := intoOpen_ι _ _ _
  have hybase : y ≫ G.X.hom = u₂ ≫ (p ⁻¹ᵁ V).ι := M.genericMap_base _ _ _ _
  have hbbase : b.left ≫ G.X.hom = u₂ ≫ (p ⁻¹ᵁ V).ι := by
    simpa only [Over.map_obj_hom, Over.mk_hom] using Over.w b
  have hyq : y₀ ≫ M.q = a₀ ≫ M.q := M.genericMap_q _ _ _ _ hy
  have hy₀ : y₀ = b₀ := by
    apply M.cartesian.hom_ext
    · exact hyq.trans hq.symm
    · apply (cancel_mono (p ⁻¹ᵁ V).ι).mp
      rw [Category.assoc, Category.assoc, morphismRestrict_ι,
        ← Category.assoc, ← Category.assoc, hyι, hbι]
      exact hybase.trans hbbase.symm
  have hyb : y = b.left := hyι.symm.trans ((congrArg (· ≫ (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι) hy₀).trans hbι)
  exact hyb

#print axioms genericMap_eq_genericPointEquiv

end ZInQ.Contrib.CloudR2NOS.GoodDescent.GroupPoints
