import Mathlib

/-!
# Spreading out, I: reflecting group-object structures along monoidal functors

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task spread-out, 2026-11-13).

Pure category theory (Mathlib only, no hypotheses).  Let `F : C ⥤ D` be a monoidal functor between
cartesian monoidal categories, `M : C` with *raw* group data `m : M ⊗ M ⟶ M`, `u : 𝟙 ⟶ M`,
`i : M ⟶ M` (no axioms).  The data induced on `F.obj M` (the formulas of `Functor.grpObjObj`)
satisfies the group axioms iff `F` identifies the two sides of each axiom for `M`
(`grpAx_map_iff`).  If the induced data is identified with a group object `N` by an isomorphism
`F.obj M ≅ N` (`Compat`), then `F` identifies both sides of each axiom (`fAx_of_compat`).
`Compat` transports along a natural isomorphism `P ⋙ F' ≅ F` (`compat_transport`), and once the
axioms hold after `P`, the group object `P.obj M` maps isomorphically onto `N`
(`isMonHom_descend`).  These are the formal steps of descending a group scheme to a finite stage
of a limit (EGA IV₃ 8.8.2 / Stacks 01ZC applied to the structure maps and the axioms).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Functor

namespace ZInQ.Contrib.SpreadOut

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {C' : Type u₃} [Category.{v₃} C'] [CartesianMonoidalCategory C']
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

/-- The group-object axioms for raw data `m, u, i` on `M` (the fields of `GrpObj`). -/
structure GrpAx {M : C} (m : M ⊗ M ⟶ M) (u : 𝟙_ C ⟶ M) (i : M ⟶ M) : Prop where
  one_mul : u ▷ M ≫ m = (λ_ M).hom
  mul_one : M ◁ u ≫ m = (ρ_ M).hom
  mul_assoc : m ▷ M ≫ m = (α_ M M M).hom ≫ M ◁ m ≫ m
  left_inv : lift i (𝟙 M) ≫ m = toUnit M ≫ u
  right_inv : lift (𝟙 M) i ≫ m = toUnit M ≫ u

/-- A `GrpObj` from raw data satisfying the axioms. -/
abbrev GrpAx.grpObj {M : C} {m : M ⊗ M ⟶ M} {u : 𝟙_ C ⟶ M} {i : M ⟶ M} (h : GrpAx m u i) :
    GrpObj M where
  one := u
  mul := m
  one_mul := h.one_mul
  mul_one := h.mul_one
  mul_assoc := h.mul_assoc
  inv := i
  left_inv := h.left_inv
  right_inv := h.right_inv

theorem grpAx_of_grpObj (M : C) [GrpObj M] : GrpAx μ[M] η[M] ι[M] :=
  ⟨MonObj.one_mul M, MonObj.mul_one M, MonObj.mul_assoc M, GrpObj.left_inv M, GrpObj.right_inv M⟩

/-- The two sides of each group axiom for `m, u, i` are identified by `F`. -/
structure FAx (F : C ⥤ D) {M : C} (m : M ⊗ M ⟶ M) (u : 𝟙_ C ⟶ M) (i : M ⟶ M) : Prop where
  one_mul : F.map (u ▷ M ≫ m) = F.map (λ_ M).hom
  mul_one : F.map (M ◁ u ≫ m) = F.map (ρ_ M).hom
  mul_assoc : F.map (m ▷ M ≫ m) = F.map ((α_ M M M).hom ≫ M ◁ m ≫ m)
  left_inv : F.map (lift i (𝟙 M) ≫ m) = F.map (toUnit M ≫ u)
  right_inv : F.map (lift (𝟙 M) i ≫ m) = F.map (toUnit M ≫ u)

section Map

variable (F : C ⥤ D) [F.Monoidal] {M : C} (m : M ⊗ M ⟶ M) (u : 𝟙_ C ⟶ M) (i : M ⟶ M)

/-- The data induced on `F.obj M` satisfies the group axioms iff `F` identifies the two sides of
each axiom for `M`. -/
theorem grpAx_map_iff :
    GrpAx (LaxMonoidal.μ F M M ≫ F.map m) (LaxMonoidal.ε F ≫ F.map u) (F.map i) ↔ FAx F m u i := by
  have h1 : (LaxMonoidal.ε F ≫ F.map u) ▷ F.obj M ≫ LaxMonoidal.μ F M M ≫ F.map m =
      (LaxMonoidal.ε F ▷ F.obj M ≫ LaxMonoidal.μ F (𝟙_ C) M) ≫ F.map (u ▷ M ≫ m) := by
    simp only [comp_whiskerRight, Category.assoc, LaxMonoidal.μ_natural_left_assoc, F.map_comp]
  have h1' : (λ_ (F.obj M)).hom =
      (LaxMonoidal.ε F ▷ F.obj M ≫ LaxMonoidal.μ F (𝟙_ C) M) ≫ F.map (λ_ M).hom := by
    rw [Category.assoc]; exact LaxMonoidal.left_unitality F M
  have h2 : F.obj M ◁ (LaxMonoidal.ε F ≫ F.map u) ≫ LaxMonoidal.μ F M M ≫ F.map m =
      (F.obj M ◁ LaxMonoidal.ε F ≫ LaxMonoidal.μ F M (𝟙_ C)) ≫ F.map (M ◁ u ≫ m) := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      LaxMonoidal.μ_natural_right_assoc, F.map_comp]
  have h2' : (ρ_ (F.obj M)).hom =
      (F.obj M ◁ LaxMonoidal.ε F ≫ LaxMonoidal.μ F M (𝟙_ C)) ≫ F.map (ρ_ M).hom := by
    rw [Category.assoc]; exact LaxMonoidal.right_unitality F M
  have h3 : (LaxMonoidal.μ F M M ≫ F.map m) ▷ F.obj M ≫ LaxMonoidal.μ F M M ≫ F.map m =
      (LaxMonoidal.μ F M M ▷ F.obj M ≫ LaxMonoidal.μ F (M ⊗ M) M) ≫ F.map (m ▷ M ≫ m) := by
    simp only [comp_whiskerRight, Category.assoc, LaxMonoidal.μ_natural_left_assoc, F.map_comp]
  have h3' : (α_ (F.obj M) (F.obj M) (F.obj M)).hom ≫
      F.obj M ◁ (LaxMonoidal.μ F M M ≫ F.map m) ≫ LaxMonoidal.μ F M M ≫ F.map m =
      (LaxMonoidal.μ F M M ▷ F.obj M ≫ LaxMonoidal.μ F (M ⊗ M) M) ≫
        F.map ((α_ M M M).hom ≫ M ◁ m ≫ m) := by
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      LaxMonoidal.μ_natural_right_assoc, F.map_comp]
    rw [← LaxMonoidal.associativity_assoc]
  have h4 : lift (F.map i) (𝟙 (F.obj M)) ≫ LaxMonoidal.μ F M M ≫ F.map m =
      F.map (lift i (𝟙 M) ≫ m) := by
    rw [← F.map_id, Monoidal.lift_μ_assoc, F.map_comp]
  have h5 : lift (𝟙 (F.obj M)) (F.map i) ≫ LaxMonoidal.μ F M M ≫ F.map m =
      F.map (lift (𝟙 M) i ≫ m) := by
    rw [← F.map_id, Monoidal.lift_μ_assoc, F.map_comp]
  have h6 : toUnit (F.obj M) ≫ LaxMonoidal.ε F ≫ F.map u = F.map (toUnit M ≫ u) := by
    rw [Monoidal.toUnit_ε_assoc, F.map_comp]
  constructor
  · rintro ⟨a1, a2, a3, a4, a5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, h1'] at a1; exact (cancel_epi _).1 a1
    · rw [h2, h2'] at a2; exact (cancel_epi _).1 a2
    · rw [h3, h3'] at a3; exact (cancel_epi _).1 a3
    · rw [h4, h6] at a4; exact a4
    · rw [h5, h6] at a5; exact a5
  · rintro ⟨a1, a2, a3, a4, a5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, h1', a1]
    · rw [h2, h2', a2]
    · rw [h3, h3', a3]
    · rw [h4, h6, a4]
    · rw [h5, h6, a5]

end Map

section Compat

variable {N : D} [GrpObj N]

/-- The multiplication induced on `F.obj M` corresponds to that of `N` under `e`. -/
def CompatM (F : C ⥤ D) [F.Monoidal] {M : C} (e : F.obj M ≅ N) (m : M ⊗ M ⟶ M) : Prop :=
  LaxMonoidal.μ F M M ≫ F.map m = (e.hom ⊗ₘ e.hom) ≫ μ[N] ≫ e.inv

/-- The unit induced on `F.obj M` corresponds to that of `N` under `e`. -/
def CompatU (F : C ⥤ D) [F.Monoidal] {M : C} (e : F.obj M ≅ N) (u : 𝟙_ C ⟶ M) : Prop :=
  LaxMonoidal.ε F ≫ F.map u = η[N] ≫ e.inv

/-- The inverse induced on `F.obj M` corresponds to that of `N` under `e`. -/
def CompatI (F : C ⥤ D) {M : C} (e : F.obj M ≅ N) (i : M ⟶ M) : Prop :=
  F.map i = e.hom ≫ ι[N] ≫ e.inv

/-- If `F` carries the raw data of `M` to the group structure of `N` (up to `e`), then `F`
identifies the two sides of each group axiom for `M`. -/
theorem fAx_of_compat (F : C ⥤ D) [F.Monoidal] {M : C} (e : F.obj M ≅ N) {m : M ⊗ M ⟶ M}
    {u : 𝟙_ C ⟶ M} {i : M ⟶ M} (hm : CompatM F e m) (hu : CompatU F e u) (hi : CompatI F e i) :
    FAx F m u i := by
  rw [← grpAx_map_iff]
  letI : GrpObj (F.obj M) := GrpObj.ofIso e.symm
  have h := grpAx_of_grpObj (F.obj M)
  have e1 : μ[F.obj M] = LaxMonoidal.μ F M M ≫ F.map m := by
    rw [hm]; rfl
  have e2 : η[F.obj M] = LaxMonoidal.ε F ≫ F.map u := by
    rw [hu]; rfl
  have e3 : ι[F.obj M] = F.map i := by
    rw [hi]; rfl
  rw [e1, e2, e3] at h
  exact h

variable (P : C ⥤ C') (F' : C' ⥤ D) (F : C ⥤ D) [P.Monoidal] [F'.Monoidal] [F.Monoidal]
  (θ : P ⋙ F' ≅ F) {M : C} (e : F.obj M ≅ N)

theorem compatM_transport {m : M ⊗ M ⟶ M} (h : CompatM F e m) :
    CompatM F' (θ.app M ≪≫ e) (LaxMonoidal.μ P M M ≫ P.map m) := by
  unfold CompatM at h ⊢
  have ht := NatTrans.IsMonoidal.tensor (τ := θ.hom) M M
  simp only [LaxMonoidal.comp_μ, Category.assoc] at ht
  have hn := θ.hom.naturality m
  simp only [Functor.comp_map] at hn
  rw [← cancel_mono (θ.hom.app M)]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, F'.map_comp]
  calc LaxMonoidal.μ F' (P.obj M) (P.obj M) ≫ F'.map (LaxMonoidal.μ P M M) ≫
          F'.map (P.map m) ≫ θ.hom.app M
        = (LaxMonoidal.μ F' (P.obj M) (P.obj M) ≫ F'.map (LaxMonoidal.μ P M M) ≫
            θ.hom.app (M ⊗ M)) ≫ F.map m := by rw [hn]; simp only [Category.assoc]
    _ = (θ.hom.app M ⊗ₘ θ.hom.app M) ≫ LaxMonoidal.μ F M M ≫ F.map m := by
        simp only [Category.assoc] at ht ⊢
        rw [reassoc_of% ht]
    _ = _ := by rw [h, tensorHom_comp_tensorHom_assoc]

theorem compatU_transport {u : 𝟙_ C ⟶ M} (h : CompatU F e u) :
    CompatU F' (θ.app M ≪≫ e) (LaxMonoidal.ε P ≫ P.map u) := by
  unfold CompatU at h ⊢
  have ht := NatTrans.IsMonoidal.unit (τ := θ.hom)
  simp only [LaxMonoidal.comp_ε, Category.assoc] at ht
  have hn := θ.hom.naturality u
  simp only [Functor.comp_map] at hn
  rw [← cancel_mono (θ.hom.app M)]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, F'.map_comp]
  calc LaxMonoidal.ε F' ≫ F'.map (LaxMonoidal.ε P) ≫ F'.map (P.map u) ≫ θ.hom.app M
        = (LaxMonoidal.ε F' ≫ F'.map (LaxMonoidal.ε P) ≫ θ.hom.app (𝟙_ C)) ≫ F.map u := by
          rw [hn]; simp only [Category.assoc]
    _ = LaxMonoidal.ε F ≫ F.map u := by rw [ht]
    _ = _ := h

theorem compatI_transport {i : M ⟶ M} (h : CompatI F e i) :
    CompatI F' (θ.app M ≪≫ e) (P.map i) := by
  unfold CompatI at h ⊢
  have hn := θ.hom.naturality i
  simp only [Functor.comp_map] at hn
  rw [← cancel_mono (θ.hom.app M)]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [hn, h]

/-- A morphism `g' : P Y ⟶ P Z` lifting `μ`-conjugate data gives a multiplication with `CompatM`. -/
theorem compatM_of_lift {g' : P.obj (M ⊗ M) ⟶ P.obj M}
    (hg : F'.map g' = θ.hom.app (M ⊗ M) ≫
      (inv (LaxMonoidal.μ F M M) ≫ (e.hom ⊗ₘ e.hom) ≫ μ[N] ≫ e.inv) ≫ θ.inv.app M) :
    CompatM F' (θ.app M ≪≫ e) (LaxMonoidal.μ P M M ≫ g') := by
  unfold CompatM
  have ht := NatTrans.IsMonoidal.tensor (τ := θ.hom) M M
  simp only [LaxMonoidal.comp_μ, Category.assoc] at ht
  rw [F'.map_comp, hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  have : LaxMonoidal.μ F' (P.obj M) (P.obj M) ≫ F'.map (LaxMonoidal.μ P M M) ≫ θ.hom.app (M ⊗ M) =
      (θ.hom.app M ⊗ₘ θ.hom.app M) ≫ LaxMonoidal.μ F M M := ht
  rw [reassoc_of% this, IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc]

theorem compatU_of_lift {g' : P.obj (𝟙_ C) ⟶ P.obj M}
    (hg : F'.map g' = θ.hom.app (𝟙_ C) ≫ (inv (LaxMonoidal.ε F) ≫ η[N] ≫ e.inv) ≫
      θ.inv.app M) :
    CompatU F' (θ.app M ≪≫ e) (LaxMonoidal.ε P ≫ g') := by
  unfold CompatU
  have ht := NatTrans.IsMonoidal.unit (τ := θ.hom)
  simp only [LaxMonoidal.comp_ε, Category.assoc] at ht
  rw [F'.map_comp, hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  have : LaxMonoidal.ε F' ≫ F'.map (LaxMonoidal.ε P) ≫ θ.hom.app (𝟙_ C) = LaxMonoidal.ε F := ht
  rw [reassoc_of% this, IsIso.hom_inv_id_assoc]

theorem compatI_of_lift {g' : P.obj M ⟶ P.obj M}
    (hg : F'.map g' = θ.hom.app M ≫ (e.hom ≫ ι[N] ≫ e.inv) ≫ θ.inv.app M) :
    CompatI F' (θ.app M ≪≫ e) g' := by
  unfold CompatI
  rw [hg]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Category.assoc]

/-- A morphism of group objects from `Compat` data: if the structure of the group object `M'`
corresponds under `F'` and `g` to that of `N`, then `g` is a monoid morphism for the image
structure `Functor.grpObjObj`. -/
theorem isMonHom_of_compat {M' : C'} [GrpObj M'] (g : F'.obj M' ≅ N)
    (hm : CompatM F' g μ[M']) (hu : CompatU F' g η[M']) :
    letI : GrpObj (F'.obj M') := Functor.grpObjObj
    IsMonHom g.hom := by
  letI : GrpObj (F'.obj M') := Functor.grpObjObj
  refine ⟨?_, ?_⟩
  · show (LaxMonoidal.ε F' ≫ F'.map η[M']) ≫ g.hom = η[N]
    rw [hu]; simp
  · show (LaxMonoidal.μ F' M' M' ≫ F'.map μ[M']) ≫ g.hom = (g.hom ⊗ₘ g.hom) ≫ μ[N]
    rw [hm]; simp

/-- A morphism of group objects `g : F.obj M ≅ N` (for the image structure) gives `CompatM`. -/
theorem compatM_of_isMonHom {M : C} [GrpObj M] (g : F.obj M ≅ N)
    (h : letI : GrpObj (F.obj M) := Functor.grpObjObj; IsMonHom g.hom) : CompatM F g μ[M] := by
  letI : GrpObj (F.obj M) := Functor.grpObjObj
  unfold CompatM
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact IsMonHom.mul_hom g.hom

/-- A morphism of group objects `g : F.obj M ≅ N` (for the image structure) gives `CompatU`. -/
theorem compatU_of_isMonHom {M : C} [GrpObj M] (g : F.obj M ≅ N)
    (h : letI : GrpObj (F.obj M) := Functor.grpObjObj; IsMonHom g.hom) : CompatU F g η[M] := by
  letI : GrpObj (F.obj M) := Functor.grpObjObj
  unfold CompatU
  rw [Iso.eq_comp_inv]
  exact IsMonHom.one_hom g.hom

/-- **Descent of a group structure.**  Raw data on `M` compatible (under `F` and `e`) with the
group object `N`, whose axioms hold after `P`, gives a group object `P.obj M` (structure maps the
images under `P`) and `θ.app M ≪≫ e : F'.obj (P.obj M) ≅ N` is a morphism of group objects. -/
theorem isMonHom_descend {m : M ⊗ M ⟶ M} {u : 𝟙_ C ⟶ M} {i : M ⟶ M}
    (hm : CompatM F e m) (hu : CompatU F e u) (_hi : CompatI F e i) (hP : FAx P m u i) :
    letI : GrpObj (P.obj M) := ((grpAx_map_iff P m u i).2 hP).grpObj
    letI : GrpObj (F'.obj (P.obj M)) := Functor.grpObjObj
    IsMonHom (θ.app M ≪≫ e : F'.obj (P.obj M) ≅ N).hom := by
  letI : GrpObj (P.obj M) := ((grpAx_map_iff P m u i).2 hP).grpObj
  exact isMonHom_of_compat F' (θ.app M ≪≫ e) (compatM_transport P F' F θ e hm)
    (compatU_transport P F' F θ e hu)

end Compat

end ZInQ.Contrib.SpreadOut
