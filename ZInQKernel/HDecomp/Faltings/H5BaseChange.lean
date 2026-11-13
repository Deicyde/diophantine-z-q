import ZInQKernel.HDecomp.Faltings.H5Neron

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5a from
`scratch/h5-neron/BaseChange.lean` (branch `wip/h5-neron` at b7c1dc21; its compiled part),
with the assembly that proves glue H4b added by hdec-adopt5a.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-! # h5-neron, part F: the glue `GroupModelBaseChangeExists` (H4b)

`IsBaseChangeOf` and `GroupModelBaseChangeExists` (copied in the draft from
`Reduction.lean`) are imported from `ZInQKernel.HDecomp.Faltings.H5Neron`. -/

namespace ZInQ.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped Obj

variable {K : Type} [Field K] {A : AbVar K}

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

/-! ### The assembly (task hdec-adopt5a)

The draft's proof of `bcGen_isMonHom` stated `(bcGen 𝒢).hom = composite` and closed it by `rfl`.
The source and target of `bcGen` are `genericFibre L' _` and `(A.baseChange L').X`, which are
not syntactically the objects of the composite, and the kernel times out on that `rfl`. Here the
isomorphism is built at the composite's own type (`genIso`, `bcGen'`), its `hom` is computed by an
explicit chain of `Iso.trans_hom` steps, and only at the end is it used at the `GroupModel` type
(a definitional unfolding of `genericFibre` and `AbVar.baseChange`). -/

section Assembly

variable {K : Type} [Field K] {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

theorem pbCompIso_hom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (pbCompIso f g G).hom = pbCompHom f g G := rfl

theorem pbCompIso_inv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (pbCompIso f g G).inv = pbCompInv f g G := rfl

theorem pbEqIso_hom {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (pbEqIso h G).hom = pbEq h G := rfl

theorem pbCompIso_symm_hom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (pbCompIso f g G).symm.hom = pbCompInv f g G := by
  rw [Iso.symm_hom, pbCompIso_inv]

/-- `𝒢.gen`, with its source and target unfolded. -/
noncomputable def genIso {A : AbVar K} (𝒢 : GroupModel A L) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)))).obj 𝒢.G ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.X :=
  𝒢.gen

theorem genIso_isMonHom {A : AbVar K} (𝒢 : GroupModel A L) : IsMonHom (genIso 𝒢).hom :=
  𝒢.gen_hom

/-- `bcGen`, at the type of the composite. -/
noncomputable def bcGen' {A : AbVar K} (𝒢 : GroupModel A L) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).obj
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G) ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L')))).obj A.X :=
  (pbCompIso _ _ 𝒢.G).symm ≪≫ pbEqIso (square1 L L') 𝒢.G ≪≫ pbCompIso _ _ 𝒢.G ≪≫
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap L L')))).mapIso (genIso 𝒢) ≪≫
    (pbCompIso _ _ A.X).symm ≪≫ pbEqIso (square2 L L') A.X

section Hom

variable {A : AbVar K} (𝒢 : GroupModel A L)
local notation "jL'" => Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L'))
local notation "φ" => Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
local notation "ψ" => Spec.map (CommRingCat.ofHom (algebraMap L L'))
local notation "jL" => Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))
local notation "κ" => Spec.map (CommRingCat.ofHom (algebraMap K L))

theorem bcGen'_eq : (bcGen' (L' := L') 𝒢).hom = ((pbCompIso _ _ 𝒢.G).symm ≪≫
    pbEqIso (square1 L L') 𝒢.G ≪≫ pbCompIso _ _ 𝒢.G ≪≫ (Over.pullback ψ).mapIso (genIso 𝒢) ≪≫
    (pbCompIso _ _ A.X).symm ≪≫ pbEqIso (square2 L L') A.X).hom := by
  rw [bcGen']

/-- The `hom` of `bcGen'` as a composite of six morphisms (an explicit chain: a single `rfl` or
`simp` here makes the kernel time out). -/
theorem bcGen'_hom : (bcGen' (L' := L') 𝒢).hom = pbCompInv _ _ 𝒢.G ≫ pbEq (square1 L L') 𝒢.G ≫
      pbCompHom _ _ 𝒢.G ≫ (Over.pullback ψ).map (genIso 𝒢).hom ≫
      pbCompInv _ _ A.X ≫ pbEq (square2 L L') A.X := by
  have e5 : ((pbCompIso ψ κ A.X).symm ≪≫ pbEqIso (square2 L L') A.X).hom =
      pbCompInv ψ κ A.X ≫ pbEq (square2 L L') A.X :=
    (Iso.trans_hom _ _).trans
      (congrArg₂ (· ≫ ·) (pbCompIso_symm_hom _ _ _) (pbEqIso_hom _ _))
  have e4 : ((Over.pullback ψ).mapIso (genIso 𝒢) ≪≫ (pbCompIso ψ κ A.X).symm ≪≫
      pbEqIso (square2 L L') A.X).hom =
      (Over.pullback ψ).map (genIso 𝒢).hom ≫ pbCompInv ψ κ A.X ≫ pbEq (square2 L L') A.X :=
    (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (Functor.mapIso_hom _ _) e5)
  have e3 : (pbCompIso ψ jL 𝒢.G ≪≫ (Over.pullback ψ).mapIso (genIso 𝒢) ≪≫
      (pbCompIso ψ κ A.X).symm ≪≫ pbEqIso (square2 L L') A.X).hom =
      pbCompHom ψ jL 𝒢.G ≫ (Over.pullback ψ).map (genIso 𝒢).hom ≫ pbCompInv ψ κ A.X ≫
        pbEq (square2 L L') A.X :=
    (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (pbCompIso_hom _ _ _) e4)
  have e2 : (pbEqIso (square1 L L') 𝒢.G ≪≫ pbCompIso ψ jL 𝒢.G ≪≫
      (Over.pullback ψ).mapIso (genIso 𝒢) ≪≫ (pbCompIso ψ κ A.X).symm ≪≫
      pbEqIso (square2 L L') A.X).hom =
      pbEq (square1 L L') 𝒢.G ≫ pbCompHom ψ jL 𝒢.G ≫ (Over.pullback ψ).map (genIso 𝒢).hom ≫
        pbCompInv ψ κ A.X ≫ pbEq (square2 L L') A.X :=
    (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (pbEqIso_hom _ _) e3)
  have e1 := (Iso.trans_hom _ _).trans (congrArg₂ (· ≫ ·) (pbCompIso_symm_hom jL' φ 𝒢.G) e2)
  exact (bcGen'_eq 𝒢).trans e1

theorem bcGen'_isMonHom : IsMonHom (bcGen' (L' := L') 𝒢).hom := by
  have hg₀ := genIso_isMonHom 𝒢
  have c1 := isMonHom_pbCompInv jL' φ 𝒢.G
  have c2 := isMonHom_pbEq (square1 L L') 𝒢.G
  have c3 := isMonHom_pbCompHom ψ jL 𝒢.G
  have c5 := isMonHom_pbCompInv ψ κ A.X
  have c6 := isMonHom_pbEq (square2 L L') A.X
  rw [bcGen'_hom]
  infer_instance

end Hom

/-- **Glue H4b (`GroupModelBaseChangeExists`), proved.** A group model `𝒢` of `A_L` over `𝓞_L`
base-changes to a group model `𝒢 ×_{𝓞_L} 𝓞_{L'}` of `A_{L'}` over `𝓞_{L'}`. -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  unfold GroupModelBaseChangeExists
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  refine ⟨⟨_, bcGen' (L' := L') 𝒢, bcGen'_isMonHom (L' := L') 𝒢⟩, Iso.refl _, ?_⟩
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)))

end Assembly

end ZInQ.H5Neron
