import ZInQKernel.HDecomp.Faltings.HodgeLattice

/-! # unif-dims: toward `ProductCotangent` — cotangent maps of unit-preserving morphisms -/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! Copied from infra-stalks (`scratch/infra-stalks/StalkPullback.lean`, origin/wip/infra-stalks
3cbf276a): stalk maps between given points. -/

/-- The stalk map of `f` from `y` to `x`, for `f x = y`. -/
noncomputable def Scheme.Hom.stalkMapAt {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) : Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ f.stalkMap x

instance {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y} (h : f x = y) :
    IsLocalHom (f.stalkMapAt h).hom := by
  unfold Scheme.Hom.stalkMapAt
  rw [CommRingCat.hom_comp]
  infer_instance

theorem Scheme.Hom.stalkMapAt_rfl {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.stalkMapAt (rfl : f x = f x) = f.stalkMap x := by
  unfold Scheme.Hom.stalkMapAt
  have : (Y.presheaf.stalkCongr (.of_eq (rfl : f x = f x).symm)).hom = 𝟙 _ :=
    Y.presheaf.stalkSpecializes_refl _
  rw [this, Category.id_comp]

theorem Scheme.Hom.stalkMapAt_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y}
    {z : Z} (hf : f x = y) (hg : g y = z) (hfg : (f ≫ g) x = z) :
    (f ≫ g).stalkMapAt hfg = g.stalkMapAt hg ≫ f.stalkMapAt hf := by
  subst hf hg
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl]
  unfold Scheme.Hom.stalkMapAt
  have : (Z.presheaf.stalkCongr (.of_eq hfg.symm)).hom = 𝟙 _ :=
    Z.presheaf.stalkSpecializes_refl _
  rw [this]
  exact (Category.id_comp _).trans (Scheme.Hom.stalkMap_comp f g x)

theorem Scheme.Hom.stalkMapAt_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) {x : X} {y : Y}
    (hf : f x = y) (hg : g x = y) : f.stalkMapAt hf = g.stalkMapAt hg := by
  subst e; rfl

theorem Scheme.Hom.stalkMapAt_id {X : Scheme.{u}} (x : X) (h : (𝟙 X) x = x) :
    Scheme.Hom.stalkMapAt (𝟙 X) h = 𝟙 _ := by
  unfold Scheme.Hom.stalkMapAt
  rw [Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (X.presheaf.stalkSpecializes_refl _)

/-- A germ of a global section, pulled back. -/
theorem Scheme.Hom.stalkMapAt_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (s : Γ(Y, ⊤)) :
    (f.stalkMapAt h).hom (Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) s) =
      X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) (f.appTop s) := by
  subst h
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.germ_stalkMap_apply]
  rfl

end AlgebraicGeometry

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

section CotMap

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- The stalk map at the generic units of a morphism of models preserving them. -/
noncomputable abbrev germMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.genStalk →+* 𝒢.genStalk :=
  (φ.left.stalkMapAt h).hom

/-- A morphism of models over `Spec 𝓞_L` is compatible with the structure maps. -/
theorem germMap_structMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (c : 𝓞 L) : germMap 𝒢 ℋ φ h (ℋ.structMap c) = 𝒢.structMap c := by
  rw [HodgeLattice.structMap_eq, HodgeLattice.structMap_eq, germMap,
    Scheme.Hom.stalkMapAt_germ_top]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- **The cotangent map** `cot_ℋ → cot_𝒢`, `df ↦ d(φ* f)`. -/
noncomputable def cotMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.cotangent →ₗ[𝓞 L] 𝒢.cotangent := by
  let ρ := germMap 𝒢 ℋ φ h
  letI : Module ℋ.genStalk 𝒢.cotangent := Module.compHom _ ρ
  let f : IsLocalRing.maximalIdeal ℋ.genStalk →ₗ[ℋ.genStalk] 𝒢.cotangent :=
    { toFun := fun x => 𝒢.dCls ⟨ρ x, map_nonunit ρ _ x.2⟩
      map_add' := fun x y => by
        simp only [GroupModel.dCls]
        have e : (⟨ρ ↑(x + y), map_nonunit ρ _ (x + y).2⟩ :
            IsLocalRing.maximalIdeal 𝒢.genStalk) =
            (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) +
              ⟨ρ y, map_nonunit ρ _ y.2⟩ := Subtype.ext (by simp)
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_add _ _ _
      map_smul' := fun r x => by
        simp only [GroupModel.dCls, RingHom.id_apply]
        have e : (⟨ρ ↑(r • x), map_nonunit ρ _ (r • x).2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
            ρ r • (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) :=
          Subtype.ext (by simp [ρ])
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_smul _ _ _ }
  let j0 : ℋ.cotangent →ₗ[ℋ.genStalk] 𝒢.cotangent := Ideal.Cotangent.lift f (fun x y => by
    refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
    show ρ (↑x * ↑y) ∈ _
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul (map_nonunit ρ _ x.2) (map_nonunit ρ _ y.2))
  exact
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun c x => by
        show j0 (ℋ.structMap c • x) = 𝒢.structMap c • j0 x
        rw [j0.map_smul]
        show ρ (ℋ.structMap c) • j0 x = _
        rw [germMap_structMap] }

theorem cotMap_dCls (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (f : IsLocalRing.maximalIdeal ℋ.genStalk) :
    cotMap 𝒢 ℋ φ h (ℋ.dCls f) =
      𝒢.dCls ⟨germMap 𝒢 ℋ φ h f, map_nonunit (germMap 𝒢 ℋ φ h) _ f.2⟩ := by
  rfl

end CotMap

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.cotMap_dCls
