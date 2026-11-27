import Mathlib

/-!
# Descending group objects along faithful monoidal functors

Let `F : C ⥤ D` be a faithful strong monoidal functor between cartesian monoidal categories.
Given `M : C` with maps `e : 𝟙_ C ⟶ M`, `m : M ⊗ M ⟶ M`, `i : M ⟶ M` and a group object
structure on `F.obj M` such that

* `F.map e = η F ≫ η[F.obj M]`,
* `F.map m = δ F M M ≫ μ[F.obj M]`,
* `F.map i = ι[F.obj M]`,

the maps `e`, `m`, `i` make `M` a group object, and the structure that `Functor.grpObjObj`
transports back to `F.obj M` is the given one.

Note on conventions: `ε F : 𝟙_ D ⟶ F.obj (𝟙_ C)` and `μ F X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`
point into `F`, so the composites that can equal `F.map e` and `F.map m` use the inverse maps
`η F` and `δ F M M`. The equivalent forms `η[F.obj M] = ε F ≫ F.map e` and
`μ[F.obj M] = μ F M M ≫ F.map m` (the shape `Functor.grpObjObj` produces) are accepted by
`grpObjOfFaithful'`.

Application: for a finite, flat, surjective morphism of schemes `qX : X ⟶ Y`, the functor
`Over.pullback qX : Over Y ⥤ Over X` is faithful, because every base change of `qX` is
flat, surjective and quasi-compact, hence an effective epimorphism, hence an epimorphism.
So a group structure on a pullback descends once the structure maps are given downstairs.
-/

noncomputable section

open CategoryTheory MonoidalCategory Limits

universe v₁ v₂ u₁ u₂ u

namespace Y3GrpObjDescent

/-! ## Monoid objects -/

section Mon

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {M : C}

/-- A monoid structure on `M` reflected from one on `F.obj M` along a faithful monoidal
functor, given the structure maps downstairs. -/
def monObjOfFaithful [F.Faithful] [MonObj (F.obj M)]
    (e : 𝟙_ C ⟶ M) (m : M ⊗ M ⟶ M)
    (hone : F.map e = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ D ⟶ F.obj M))
    (hmul : F.map m =
      Functor.OplaxMonoidal.δ F M M ≫ (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M)) :
    MonObj M where
  one := e
  mul := m
  one_mul := by
    apply F.map_injective
    first
      | (simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight, hmul, hone,
          Functor.Monoidal.map_leftUnitor, MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.Monoidal.μ_δ_assoc, MonObj.one_mul]; done)
      | (simp [hmul, hone]; done)
  mul_one := by
    apply F.map_injective
    first
      | (simp only [Functor.map_comp, Functor.Monoidal.map_whiskerLeft, hmul, hone,
          Functor.Monoidal.map_rightUnitor, MonoidalCategory.whiskerLeft_comp, Category.assoc,
          Functor.Monoidal.μ_δ_assoc, MonObj.mul_one]; done)
      | (simp [hmul, hone]; done)
  mul_assoc := by
    have hW : ∀ {Z : D} (h : F.obj M ⊗ (F.obj M ⊗ F.obj M) ⟶ Z),
        F.obj M ◁ Functor.LaxMonoidal.μ F M M ≫ F.obj M ◁ Functor.OplaxMonoidal.δ F M M ≫ h =
          h := by
      intro Z h
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, Functor.Monoidal.μ_δ,
        MonoidalCategory.whiskerLeft_id, Category.id_comp]
    apply F.map_injective
    first
      | (simp only [Functor.map_comp, Functor.Monoidal.map_whiskerRight,
          Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_associator, hmul,
          MonoidalCategory.comp_whiskerRight, MonoidalCategory.whiskerLeft_comp,
          Category.assoc, Functor.Monoidal.μ_δ_assoc, hW, MonObj.mul_assoc]; done)
      | (simp [hmul, hW]; done)

/-- The monoid structure transported along `F` from the reflected one is the given one. -/
theorem monObjObj_monObjOfFaithful [F.Faithful] [S : MonObj (F.obj M)]
    (e : 𝟙_ C ⟶ M) (m : M ⊗ M ⟶ M)
    (hone : F.map e = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ D ⟶ F.obj M))
    (hmul : F.map m =
      Functor.OplaxMonoidal.δ F M M ≫ (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M)) :
    letI := monObjOfFaithful F e m hone hmul
    Functor.monObjObj (F := F) M = S := by
  apply MonObj.ext
  show Functor.LaxMonoidal.μ F M M ≫ F.map m = _
  rw [hmul, Functor.Monoidal.μ_δ_assoc]

/-- Converts the unit condition from the transport form to the form used above. -/
theorem map_one_eq_of_one_eq [MonObj (F.obj M)] (e : 𝟙_ C ⟶ M)
    (h : (MonObj.one : 𝟙_ D ⟶ F.obj M) = Functor.LaxMonoidal.ε F ≫ F.map e) :
    F.map e = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ D ⟶ F.obj M) := by
  rw [h, Functor.Monoidal.η_ε_assoc]

/-- Converts the multiplication condition from the transport form to the form used above. -/
theorem map_mul_eq_of_mul_eq [MonObj (F.obj M)] (m : M ⊗ M ⟶ M)
    (h : (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M) =
      Functor.LaxMonoidal.μ F M M ≫ F.map m) :
    F.map m =
      Functor.OplaxMonoidal.δ F M M ≫ (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M) := by
  rw [h, Functor.Monoidal.δ_μ_assoc]

end Mon

/-! ## Group objects -/

section Grp

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] {M : C}

/-- A group structure on `M` reflected from one on `F.obj M` along a faithful monoidal
functor between cartesian monoidal categories, given the structure maps downstairs. -/
def grpObjOfFaithful [F.Faithful] [S : GrpObj (F.obj M)]
    (e : 𝟙_ C ⟶ M) (m : M ⊗ M ⟶ M) (i : M ⟶ M)
    (hone : F.map e = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ D ⟶ F.obj M))
    (hmul : F.map m =
      Functor.OplaxMonoidal.δ F M M ≫ (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M))
    (hinv : F.map i = (GrpObj.inv : F.obj M ⟶ F.obj M)) :
    GrpObj M :=
  { toMonObj := monObjOfFaithful F e m hone hmul
    inv := i
    left_inv := by
      have hu : ∀ {Z : D} (h : 𝟙_ D ⟶ Z),
          F.map (SemiCartesianMonoidalCategory.toUnit M) ≫ Functor.OplaxMonoidal.η F ≫ h =
            SemiCartesianMonoidalCategory.toUnit (F.obj M) ≫ h := by
        intro Z h
        rw [← Category.assoc,
          SemiCartesianMonoidalCategory.toUnit_unique
            (F.map (SemiCartesianMonoidalCategory.toUnit M) ≫ Functor.OplaxMonoidal.η F)
            (SemiCartesianMonoidalCategory.toUnit (F.obj M))]
      show CartesianMonoidalCategory.lift i (𝟙 M) ≫ m =
        SemiCartesianMonoidalCategory.toUnit M ≫ e
      apply F.map_injective
      first
        | (simp only [Functor.map_comp, hmul, hone, Functor.OplaxMonoidal.lift_δ_assoc, hinv,
            Functor.map_id, GrpObj.left_inv, hu]; done)
        | (simp [hmul, hone, hinv, hu]; done)
    right_inv := by
      have hu : ∀ {Z : D} (h : 𝟙_ D ⟶ Z),
          F.map (SemiCartesianMonoidalCategory.toUnit M) ≫ Functor.OplaxMonoidal.η F ≫ h =
            SemiCartesianMonoidalCategory.toUnit (F.obj M) ≫ h := by
        intro Z h
        rw [← Category.assoc,
          SemiCartesianMonoidalCategory.toUnit_unique
            (F.map (SemiCartesianMonoidalCategory.toUnit M) ≫ Functor.OplaxMonoidal.η F)
            (SemiCartesianMonoidalCategory.toUnit (F.obj M))]
      show CartesianMonoidalCategory.lift (𝟙 M) i ≫ m =
        SemiCartesianMonoidalCategory.toUnit M ≫ e
      apply F.map_injective
      first
        | (simp only [Functor.map_comp, hmul, hone, Functor.OplaxMonoidal.lift_δ_assoc, hinv,
            Functor.map_id, GrpObj.right_inv, hu]; done)
        | (simp [hmul, hone, hinv, hu]; done) }

/-- Variant of `grpObjOfFaithful` taking the hypotheses in the shape that
`Functor.grpObjObj` produces. -/
def grpObjOfFaithful' [F.Faithful] [S : GrpObj (F.obj M)]
    (e : 𝟙_ C ⟶ M) (m : M ⊗ M ⟶ M) (i : M ⟶ M)
    (hone : (MonObj.one : 𝟙_ D ⟶ F.obj M) = Functor.LaxMonoidal.ε F ≫ F.map e)
    (hmul : (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M) =
      Functor.LaxMonoidal.μ F M M ≫ F.map m)
    (hinv : (GrpObj.inv : F.obj M ⟶ F.obj M) = F.map i) :
    GrpObj M :=
  grpObjOfFaithful F e m i (map_one_eq_of_one_eq F e hone) (map_mul_eq_of_mul_eq F m hmul)
    hinv.symm

/-- The group structure transported along `F` from the reflected one is the given one. -/
theorem grpObjObj_grpObjOfFaithful [F.Faithful] [S : GrpObj (F.obj M)]
    (e : 𝟙_ C ⟶ M) (m : M ⊗ M ⟶ M) (i : M ⟶ M)
    (hone : F.map e = Functor.OplaxMonoidal.η F ≫ (MonObj.one : 𝟙_ D ⟶ F.obj M))
    (hmul : F.map m =
      Functor.OplaxMonoidal.δ F M M ≫ (MonObj.mul : F.obj M ⊗ F.obj M ⟶ F.obj M))
    (hinv : F.map i = (GrpObj.inv : F.obj M ⟶ F.obj M)) :
    letI := grpObjOfFaithful F e m i hone hmul hinv
    Functor.grpObjObj (F := F) (G := M) = S := by
  apply GrpObj.ext
  apply MonObj.ext
  show Functor.LaxMonoidal.μ F M M ≫ F.map m = _
  rw [hmul, Functor.Monoidal.μ_δ_assoc]

end Grp

/-! ## Pullback along a finite, flat, surjective morphism of schemes -/

section Schemes

open AlgebraicGeometry

variable {X Y : Scheme.{u}} (qX : X ⟶ Y) [IsFinite qX] [Flat qX] [Surjective qX]

/-- Every base change of a finite, flat, surjective morphism is an epimorphism. -/
theorem epi_pullback_fst_of_finite_flat_surjective (U : Over Y) :
    Epi (pullback.fst U.hom qX) := by
  have sq : IsPullback (pullback.snd U.hom qX) (pullback.fst U.hom qX) qX U.hom :=
    (IsPullback.of_hasPullback U.hom qX).flip
  haveI : Flat (pullback.fst U.hom qX) :=
    MorphismProperty.of_isPullback (P := @Flat) sq (inferInstance : Flat qX)
  haveI : Surjective (pullback.fst U.hom qX) :=
    MorphismProperty.of_isPullback (P := @Surjective) sq (inferInstance : Surjective qX)
  haveI : IsFinite (pullback.fst U.hom qX) :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq (inferInstance : IsFinite qX)
  haveI : QuasiCompact (pullback.fst U.hom qX) := inferInstance
  haveI : EffectiveEpi (pullback.fst U.hom qX) := by
    first
      | exact inferInstance
      | exact Scheme.instEffectiveEpiOfQuasiCompactOfSurjectiveOfFlat _
  exact epi_of_effectiveEpi _

/-- Two parallel maps in `Over Y` with equal pullbacks along `qX` are equal. -/
theorem hom_ext_of_pullback_map_eq {U V : Over Y} {u v : U ⟶ V}
    (h : (Over.pullback qX).map u = (Over.pullback qX).map v) : u = v := by
  haveI := epi_pullback_fst_of_finite_flat_surjective qX U
  have h1 : ((Over.pullback qX).map u).left ≫ pullback.fst V.hom qX =
      ((Over.pullback qX).map v).left ≫ pullback.fst V.hom qX := by
    rw [h]
  have h2 : pullback.fst U.hom qX ≫ u.left = pullback.fst U.hom qX ≫ v.left := by
    first
      | (simpa only [Over.pullback_map_left, pullback.lift_fst] using h1)
      | (simpa using h1)
  exact Over.OverMorphism.ext ((cancel_epi (pullback.fst U.hom qX)).1 h2)

instance faithful_overPullback : (Over.pullback qX).Faithful where
  map_injective := by
    intro U V u v h
    exact hom_ext_of_pullback_map_eq qX h

/-- Descent of a group object along pullback by a finite, flat, surjective morphism. -/
def grpObjOverOfPullback {B : Scheme.{u}} (b : B ⟶ Y)
    [S : GrpObj ((Over.pullback qX).obj (Over.mk b))]
    (oneB : 𝟙_ (Over Y) ⟶ Over.mk b) (mulB : Over.mk b ⊗ Over.mk b ⟶ Over.mk b)
    (invB : Over.mk b ⟶ Over.mk b)
    (hone : (Over.pullback qX).map oneB = Functor.OplaxMonoidal.η (Over.pullback qX) ≫
      (MonObj.one : 𝟙_ (Over X) ⟶ (Over.pullback qX).obj (Over.mk b)))
    (hmul : (Over.pullback qX).map mulB =
      Functor.OplaxMonoidal.δ (Over.pullback qX) (Over.mk b) (Over.mk b) ≫
        (MonObj.mul : (Over.pullback qX).obj (Over.mk b) ⊗ (Over.pullback qX).obj (Over.mk b) ⟶
          (Over.pullback qX).obj (Over.mk b)))
    (hinv : (Over.pullback qX).map invB =
      (GrpObj.inv : (Over.pullback qX).obj (Over.mk b) ⟶ (Over.pullback qX).obj (Over.mk b))) :
    GrpObj (Over.mk b) :=
  grpObjOfFaithful (Over.pullback qX) oneB mulB invB hone hmul hinv

/-- The group structure on the pullback induced by the descended one is the given one. -/
theorem grpObjObj_grpObjOverOfPullback {B : Scheme.{u}} (b : B ⟶ Y)
    [S : GrpObj ((Over.pullback qX).obj (Over.mk b))]
    (oneB : 𝟙_ (Over Y) ⟶ Over.mk b) (mulB : Over.mk b ⊗ Over.mk b ⟶ Over.mk b)
    (invB : Over.mk b ⟶ Over.mk b)
    (hone : (Over.pullback qX).map oneB = Functor.OplaxMonoidal.η (Over.pullback qX) ≫
      (MonObj.one : 𝟙_ (Over X) ⟶ (Over.pullback qX).obj (Over.mk b)))
    (hmul : (Over.pullback qX).map mulB =
      Functor.OplaxMonoidal.δ (Over.pullback qX) (Over.mk b) (Over.mk b) ≫
        (MonObj.mul : (Over.pullback qX).obj (Over.mk b) ⊗ (Over.pullback qX).obj (Over.mk b) ⟶
          (Over.pullback qX).obj (Over.mk b)))
    (hinv : (Over.pullback qX).map invB =
      (GrpObj.inv : (Over.pullback qX).obj (Over.mk b) ⟶ (Over.pullback qX).obj (Over.mk b))) :
    letI := grpObjOverOfPullback qX b oneB mulB invB hone hmul hinv
    Functor.grpObjObj (F := Over.pullback qX) (G := Over.mk b) = S :=
  grpObjObj_grpObjOfFaithful (Over.pullback qX) oneB mulB invB hone hmul hinv

end Schemes

end Y3GrpObjDescent
