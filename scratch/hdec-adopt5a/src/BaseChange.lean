import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-neron, part F: toward the glue `GroupModelBaseChangeExists` (partial)

`IsBaseChangeOf` and `GroupModelBaseChangeExists` are copied from `Reduction.lean`. -/

namespace ZInQ.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped Obj

variable {K : Type} [Field K] {A : AbVar K}

/-- (copied) -/
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- (copied) -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

/-- `(f ≫ g)^* G → f^* g^* G`, with the iterated target type. -/
noncomputable def pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ⟶ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  (Over.pullbackComp f g).hom.app G

/-- `f^* g^* G → (f ≫ g)^* G`. -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

/-- `f^* G ≅ g^* G` for `f = g`. -/
noncomputable def pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (Over.pullback f).obj G ≅ (Over.pullback g).obj G :=
  eqToIso (by subst h; rfl)

/-- `f^* G → g^* G` for `f = g`. -/
noncomputable def pbEq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (Over.pullback f).obj G ⟶ (Over.pullback g).obj G :=
  (pbEqIso h G).hom

/-- The components of `Over.pullbackComp` are monoid morphisms (for the iterated structure). -/
theorem isMonHom_pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompHom f g G) := by
  have h := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app (Mon.mk G) ≫
    (Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app
      (Mon.mk G)).isMonHom_hom
  have e : pbCompHom f g G = pbCompHom f g G ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [e]
  exact h

theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

theorem isMonHom_pbEq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y)
    [MonObj G] : IsMonHom (pbEq h G) := by
  subst h
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj G)))

/-- `(f ≫ g)^* G ≅ f^* g^* G` with explicit components. -/
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  ⟨pbCompHom f g G, pbCompInv f g G, ((Over.pullbackComp f g).app G).hom_inv_id,
    ((Over.pullbackComp f g).app G).inv_hom_id⟩

section BC

variable {K : Type} [Field K] (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

theorem square1 :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem square2 :
    Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

variable {L L'} in
/-- The identification of the generic fibre of `𝒢 ×_{𝓞_L} 𝓞_{L'}` with `A_{L'}`. -/
noncomputable def bcGen {A : AbVar K} (𝒢 : GroupModel A L) :
    genericFibre L' ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
      𝒢.G) ≅ (A.baseChange L').X :=
  (pbCompIso _ _ 𝒢.G).symm ≪≫ pbEqIso (square1 L L') 𝒢.G ≪≫ pbCompIso _ _ 𝒢.G ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L')))).mapIso 𝒢.gen ≪≫
    (pbCompIso _ _ A.X).symm ≪≫ pbEqIso (square2 L L') A.X

end BC

/-! ### Unfinished: the assembly (kernel deterministic timeout)

The following proof is accepted by the elaborator (≈50 s) but the kernel reports a
`deterministic timeout` on `bcGen_isMonHom` (the final `exact this`, a definitional check between
the instance terms of `genericFibre`/`AbVar.baseChange` and the iterated `Functor.monObjObj`).
Kept as a comment for the next attempt.

```
variable {L L'} in
theorem bcGen_isMonHom {A : AbVar K} (𝒢 : GroupModel A L) :
    letI : GrpObj (genericFibre L' ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)) := Functor.grpObjObj
    IsMonHom (bcGen (L' := L') 𝒢).hom := by
  let g₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒢.G ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X := 𝒢.gen.hom
  have hg₀ : IsMonHom g₀ := 𝒢.gen_hom
  have c1 := isMonHom_pbCompInv (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))) 𝒢.G
  have c2 := isMonHom_pbEq (square1 L L') 𝒢.G
  have c3 := isMonHom_pbCompHom (Spec.map (CommRingCat.ofHom (algebraMap L L')))
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))) 𝒢.G
  have c5 := isMonHom_pbCompInv (Spec.map (CommRingCat.ofHom (algebraMap L L')))
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) A.X
  have c6 := isMonHom_pbEq (square2 L L') A.X
  have : IsMonHom (pbCompInv _ _ 𝒢.G ≫ pbEq (square1 L L') 𝒢.G ≫ pbCompHom _ _ 𝒢.G ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L')))).map g₀ ≫
      pbCompInv _ _ A.X ≫ pbEq (square2 L L') A.X) := inferInstance
  have e : (bcGen (L' := L') 𝒢).hom = pbCompInv _ _ 𝒢.G ≫ pbEq (square1 L L') 𝒢.G ≫
      pbCompHom _ _ 𝒢.G ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L')))).map g₀ ≫
      pbCompInv _ _ A.X ≫ pbEq (square2 L L') A.X := by
    simp only [bcGen, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rfl
  rw [e]
  exact this


/ -- **Glue H4b, proved.** - /
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  unfold GroupModelBaseChangeExists
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  refine ⟨⟨_, bcGen (L' := L') 𝒢, bcGen_isMonHom (L' := L') 𝒢⟩, Iso.refl _, ?_⟩
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)))

```
-/

end ZInQ.H5Neron


#print axioms ZInQ.H5Neron.isMonHom_pbCompHom
#print axioms ZInQ.H5Neron.isMonHom_pbCompInv
#print axioms ZInQ.H5Neron.isMonHom_pbEq
#print axioms ZInQ.H5Neron.square1
#print axioms ZInQ.H5Neron.bcGen
