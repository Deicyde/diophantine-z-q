import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: combined file (self-contained; Mathlib + project only; no `sorry`, no `axiom`)

Parts (each also compiles alone in `scratch/h5-glue/`):
* §1 `BaseChange.lean`: glue H4b `GroupModelBaseChangeExists`, **proved**.
* §2 `Minimal.lean`: the Néron comparison map is a homomorphism and a generic isomorphism;
  `NeronModelMinimal` from the glue `HeightAntitone`.
* §3 `OpenSub.lean`: an open immersion of group models is an isomorphism on generic fibres, **proved**.
* §4 `Pts.lean`: a generic isomorphism is bijective on complex points, **proved**.
* §5 statements copied verbatim from `scratch/h5-neron/H5Neron.lean` (leaves N1, N2; glue H4a, M6;
  `compositum` with its proof), `OpenSubgroupHeight` from `HeightAntitone` and
  `OpenImmersionHeightLe`, and H5 in the multi-field form R19-R21 need from N1, N2 and the three
  remaining glue statements `HeightAntitone`, `OpenImmersionHeightLe`, `ModelHeightBaseChange`. -/

set_option linter.style.haveILetI false

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open scoped Obj

/-! ## §1 Base change of group models -/



/-- (copied from h5-neron) -/
def IsBaseChangeOf {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L]
    [Algebra K L] [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) : Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- (copied from h5-neron) **Glue H4b.** -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

section Abstract

variable {S S' T T' B : Scheme.{0}}

/-- `(f ≫ g)^* G → f^* g^* G`, with the iterated target type. (copied from h5-neron) -/
noncomputable def pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ⟶ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  (Over.pullbackComp f g).hom.app G

/-- `f^* g^* G → (f ≫ g)^* G`. (copied from h5-neron) -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompHom {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompHom f g G) := by
  have h := ((Functor.mapMonNatIso (Over.pullbackComp f g)).hom.app (Mon.mk G) ≫
    (Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).hom.app
      (Mon.mk G)).isMonHom_hom
  have e : pbCompHom f g G = pbCompHom f g G ≫ 𝟙 _ := (Category.comp_id _).symm
  rw [e]
  exact h

/-- (copied from h5-neron) -/
theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- `(f ≫ g)^* G ≅ f^* g^* G` with explicit components. (copied from h5-neron) -/
noncomputable def pbCompIso {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback (f ≫ g)).obj G ≅ (Over.pullback f).obj ((Over.pullback g).obj G) :=
  ⟨pbCompHom f g G, pbCompInv f g G, ((Over.pullbackComp f g).app G).hom_inv_id,
    ((Over.pullbackComp f g).app G).inv_hom_id⟩

/-- `f^* G ≅ g^* G` for `f = g`. -/
noncomputable def pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y) :
    (Over.pullback f).obj G ≅ (Over.pullback g).obj G :=
  eqToIso (by subst h; rfl)

theorem isMonHom_pbEqIso {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (G : Over Y)
    [MonObj G] : IsMonHom (pbEqIso h G).hom := by
  subst h
  exact (inferInstance : IsMonHom (𝟙 ((Over.pullback f).obj G)))

/-- The generic-fibre identification of a base change, for abstract morphisms:
`a^* b^* G ≅ (a ≫ b)^* G = (c ≫ d)^* G ≅ c^* d^* G ≅ c^* k^* X ≅ (c ≫ k)^* X = k'^* X`. -/
noncomputable def genBC (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) (X : Over B)
    (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X) :
    (Over.pullback a).obj ((Over.pullback b).obj G) ≅ (Over.pullback k').obj X :=
  (pbCompIso a b G).symm ≪≫ pbEqIso h1 G ≪≫ pbCompIso c d G ≪≫
    (Over.pullback c).mapIso gen ≪≫ (pbCompIso c k X).symm ≪≫ pbEqIso h2 X

theorem genBC_isMonHom (a : T' ⟶ S') (b : S' ⟶ S) (c : T' ⟶ T) (d : T ⟶ S) (k : T ⟶ B)
    (k' : T' ⟶ B) (h1 : a ≫ b = c ≫ d) (h2 : c ≫ k = k') (G : Over S) [GrpObj G] (X : Over B)
    [GrpObj X] (gen : (Over.pullback d).obj G ≅ (Over.pullback k).obj X)
    (hgen : letI : GrpObj ((Over.pullback d).obj G) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback k).obj X) := Functor.grpObjObj
      IsMonHom gen.hom) :
    letI : GrpObj ((Over.pullback b).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback a).obj ((Over.pullback b).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback k').obj X) := Functor.grpObjObj
    IsMonHom (genBC a b c d k k' h1 h2 G X gen).hom := by
  have c1 := isMonHom_pbCompInv a b G
  have c2 := isMonHom_pbEqIso h1 G
  have c3 := isMonHom_pbCompHom c d G
  have c5 := isMonHom_pbCompInv c k X
  have c6 := isMonHom_pbEqIso h2 X
  have c4 : IsMonHom ((Over.pullback c).map gen.hom) := inferInstance
  have e : (genBC a b c d k k' h1 h2 G X gen).hom = pbCompInv a b G ≫ (pbEqIso h1 G).hom ≫
      pbCompHom c d G ≫ (Over.pullback c).map gen.hom ≫ pbCompInv c k X ≫ (pbEqIso h2 X).hom :=
    rfl
  rw [e]
  infer_instance

end Abstract

section Concrete

variable {K : Type} [Field K] (L L' : Type) [Field L] [Algebra K L]
    [Field L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']

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

variable [NumberField L] [NumberField L']

/-- The base change `𝒢 ×_{𝓞_L} 𝓞_{L'}` of a group model, as a group model of `A_{L'}`. -/
noncomputable def GroupModel.baseChange {A : AbVar K} (𝒢 : GroupModel A L) : GroupModel A L' :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  { G := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G
    gen := genBC _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
    gen_hom := genBC_isMonHom _ _ _ _ _ _ (square1 L L') (square2 L L') 𝒢.G A.X 𝒢.gen
      𝒢.gen_hom }

/-- **Glue H4b, proved.** -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  refine ⟨GroupModel.baseChange L L' 𝒢, Iso.refl (GroupModel.baseChange L L' 𝒢).G, ?_⟩
  exact (inferInstance : IsMonHom (𝟙 (GroupModel.baseChange L L' 𝒢).G))

end Concrete


/-! ## §2 Néron minimality from `HeightAntitone` -/



section Abstract

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal functor that is injective on `Hom(𝟙, Y)` and `Hom(X ⊗ X, Y)` reflects
monoid morphisms `X → Y`. -/
theorem isMonHom_of_map {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)]
    (h1 : ∀ g g' : 𝟙_ C ⟶ Y, F.map g = F.map g' → g = g')
    (h2 : ∀ g g' : X ⊗ X ⟶ Y, F.map g = F.map g' → g = g') : IsMonHom f where
  one_hom := by
    apply h1
    rw [← cancel_epi (Functor.LaxMonoidal.ε F), F.map_comp, ← Category.assoc]
    exact IsMonHom.one_hom (f := F.map f)
  mul_hom := by
    apply h2
    rw [← cancel_epi (Functor.LaxMonoidal.μ F X X), F.map_comp, ← Category.assoc]
    have hm := IsMonHom.mul_hom (f := F.map f)
    refine hm.trans ?_
    rw [F.map_comp, Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc]

end Abstract

section Neron

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

instance smooth_tensor (𝒢 : GroupModel A L) : Smooth (𝒢.G ⊗ 𝒢.G).hom := by
  show Smooth (pullback.fst 𝒢.G.hom 𝒢.G.hom ≫ 𝒢.G.hom); infer_instance

instance smooth_unit : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L))))).hom := by
  dsimp; infer_instance

/-- The comparison map `𝒢 → 𝒩` to a Néron model (unique with `F(f) ≫ gen_𝒩 = gen_𝒢`). -/
theorem neron_lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃ f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  (h𝒩 𝒢.G).2 𝒢.gen.hom

/-- Injectivity of `F = Over.pullback (jL L)` on maps from a smooth scheme into a Néron model. -/
theorem neron_map_injective {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    {Y : Over (Spec (CommRingCat.of (𝓞 L)))} [Smooth Y.hom] (g g' : Y ⟶ 𝒩.G)
    (h : (Over.pullback (jL L)).map g = (Over.pullback (jL L)).map g') : g = g' :=
  (h𝒩 Y).1 (by simp only [h])

/-- **The Néron comparison map is a homomorphism of group schemes**, and an isomorphism on
generic fibres. -/
theorem neron_lift_isMonHom {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    (hf : (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom) :
    IsMonHom f ∧ IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  let e₂ : F.obj 𝒩.G ≅ (A.baseChange L).X := 𝒩.gen
  have g1 : IsMonHom e₁.hom := 𝒢.gen_hom
  have g2 : IsMonHom e₂.hom := 𝒩.gen_hom
  have hiso : F.map f = e₁.hom ≫ e₂.inv := by
    rw [Iso.eq_comp_inv]; exact hf
  refine ⟨?_, by rw [hiso]; infer_instance⟩
  have : IsMonHom (F.map f) := by rw [hiso]; infer_instance
  exact isMonHom_of_map F f (fun g g' => neron_map_injective h𝒩 g g')
    (fun g g' => neron_map_injective h𝒩 g g')

/-- **Glue (stated): heights decrease along generic isomorphisms.** If `f : 𝒢 → 𝒩` is a
homomorphism of group models of `A_L` that is an isomorphism on generic fibres, then
`h(𝒩) ≤ h(𝒢)`: `f*` identifies `ω_{A_L}` for both models and maps `ω_𝒩` into `ω_𝒢` (so
`⋀^g ω_𝒩 ⊆ ⋀^g ω_𝒢` and `HodgeData.modelHeight_le_of_le` applies), and `Φ ↦ f ∘ Φ` transports
analytic uniformizations with the same Jacobian determinants. -/
def HeightAntitone : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height

/-- **`NeronModelMinimal` from `HeightAntitone`.** -/
theorem neronModelMinimal_of_heightAntitone (h : HeightAntitone) : NeronModelMinimal := by
  intro K _ A L _ _ _ 𝒩 𝒢 h𝒩
  obtain ⟨f, hf⟩ := neron_lift h𝒩 𝒢
  obtain ⟨hm, hi⟩ := neron_lift_isMonHom h𝒩 𝒢 f hf
  exact h K A L 𝒢 𝒩 f hm hi

end Neron


/-! ## §3 Open subgroup models are generic isomorphisms -/

section OpenSubSec



variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]


/-- The base change of an open immersion along any `j` is an open immersion (for `Over.pullback`). -/
theorem isOpenImmersion_pullback_map {S S' : Scheme.{0}} (j : S' ⟶ S) {U G : Over S} (f : U ⟶ G)
    [IsOpenImmersion f.left] : IsOpenImmersion ((Over.pullback j).map f).left := by
  have t : IsPullback (pullback.fst G.hom j) (pullback.snd G.hom j) G.hom j :=
    IsPullback.of_hasPullback _ _
  have p : pullback.fst U.hom j ≫ f.left = ((Over.pullback j).map f).left ≫ pullback.fst G.hom j := by
    simp
  have s : IsPullback (pullback.fst U.hom j) (((Over.pullback j).map f).left ≫ pullback.snd G.hom j)
      (f.left ≫ G.hom) j := by
    have e1 : ((Over.pullback j).map f).left ≫ pullback.snd G.hom j = pullback.snd U.hom j := by
      simp
    have e2 : f.left ≫ G.hom = U.hom := Over.w f
    rw [e1, e2]
    exact IsPullback.of_hasPullback _ _
  have sq := IsPullback.of_bot s p t
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›

/-- An open immersion `h : X → X` over `Spec L` of an abelian variety is an isomorphism. -/
theorem isIso_of_openImmersion_self (B : AbVar L) (h : B.X ⟶ B.X) [IsOpenImmersion h.left] :
    IsIso h := by
  have hw : h.left ≫ B.X.hom = B.X.hom := Over.w h
  haveI : UniversallyClosed (h.left ≫ B.X.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed h.left := UniversallyClosed.of_comp_of_isSeparated h.left B.X.hom
  haveI : IrreducibleSpace B.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton B.X.hom
  have hrange : Set.range h.left = Set.univ := by
    have hc : IsClosed (Set.range h.left) := h.left.isClosedMap.isClosed_range
    have ho : IsOpen (Set.range h.left) := h.left.isOpenEmbedding.isOpen_range
    obtain ⟨x⟩ := (inferInstance : Nonempty B.X.left)
    exact IsClopen.eq_univ ⟨hc, ho⟩ ⟨h.left x, x, rfl⟩
  haveI : Surjective h.left := ⟨fun y => by
    have : y ∈ Set.range h.left := hrange ▸ Set.mem_univ y
    exact this⟩
  haveI : IsIso h.left := (isIso_iff_isOpenImmersion_and_surjective h.left).mpr ⟨‹_›, ‹_›⟩
  haveI : IsIso ((Over.forget _).map h) := inferInstanceAs (IsIso h.left)
  exact isIso_of_reflects_iso h (Over.forget _)

/-- **Open subgroup models agree generically** (proved). -/
theorem genericIso_of_openImmersion (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G)
    [IsOpenImmersion f.left] : IsIso ((Over.pullback (jL L)).map f) := by
  let F := Over.pullback (jL L)
  let e₁ : F.obj 𝒰.G ≅ (A.baseChange L).X := 𝒰.gen
  let e₂ : F.obj 𝒢.G ≅ (A.baseChange L).X := 𝒢.gen
  haveI : IsOpenImmersion (F.map f).left := isOpenImmersion_pullback_map (jL L) f
  let h : (A.baseChange L).X ⟶ (A.baseChange L).X := e₁.inv ≫ F.map f ≫ e₂.hom
  haveI : IsIso e₁.inv.left := Functor.map_isIso (Over.forget _) e₁.inv
  haveI : IsIso e₂.hom.left := Functor.map_isIso (Over.forget _) e₂.hom
  haveI : IsOpenImmersion h.left := by
    show IsOpenImmersion (e₁.inv.left ≫ (F.map f).left ≫ e₂.hom.left)
    infer_instance
  haveI := isIso_of_openImmersion_self (A.baseChange L) h
  have : F.map f = e₁.hom ≫ h ≫ e₂.inv := by
    simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [this]
  infer_instance


end OpenSubSec

/-! ## §4 Complex points along generic isomorphisms -/

section PtsSec



variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]


/-- `ptC τ = Over.map (jL L) (Spec ℂ over L via τ)`. -/
noncomputable def ptCIso (τ : L →+* ℂ) :
    GroupModel.ptC (L := L) τ ≅ (Over.map (jL L)).obj (Over.mk (Spec.map (CommRingCat.ofHom τ))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- Complex points of a group model are complex points of its generic fibre. -/
noncomputable def ptsEquiv (𝒢 : GroupModel A L) (τ : L →+* ℂ) :
    𝒢.Pts τ ≃ (Over.mk (Spec.map (CommRingCat.ofHom τ)) ⟶ (Over.pullback (jL L)).obj 𝒢.G) :=
  ((ptCIso τ).homCongr (Iso.refl 𝒢.G)).trans ((Over.mapPullbackAdj (jL L)).homEquiv _ _)

theorem ptsEquiv_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    ptsEquiv 𝒩 τ (p ≫ f) = ptsEquiv 𝒢 τ p ≫ (Over.pullback (jL L)).map f := by
  simp only [ptsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **A morphism of group models that is an isomorphism on generic fibres is bijective on
complex points** (at every `τ : L → ℂ`). -/
theorem pts_comp_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) :
    Function.Bijective (fun p : 𝒢.Pts τ => p ≫ f) := by
  have key : (fun p : 𝒢.Pts τ => p ≫ f) = (ptsEquiv 𝒩 τ).symm ∘
      (fun q => q ≫ (Over.pullback (jL L)).map f) ∘ ptsEquiv 𝒢 τ := by
    funext p
    simp only [Function.comp, ← ptsEquiv_comp, Equiv.symm_apply_apply]
  rw [key]
  refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
  exact ⟨fun a b h => (cancel_mono _).mp h, fun c => ⟨c ≫ inv ((Over.pullback (jL L)).map f),
    by simp⟩⟩


end PtsSec

/-! ## §5 Copied statements (verbatim from `scratch/h5-neron/H5Neron.lean`) and the reduction -/

section Reduction

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒰 → 𝒢` is an open immersion of group schemes over `𝓞_L`. -/
def IsOpenSubgroupModel {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) : Prop :=
  ∃ f : 𝒰.G ⟶ 𝒢.G, IsOpenImmersion f.left ∧ IsMonHom f

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- **Leaf N2 (semistable reduction and base change of the identity component).** For `A` over
a number field `K` there are a finite extension `L₀/K` and a Néron model `𝒩₀` over `𝓞_{L₀}` such
that for every finite extension `L'/L₀` and every Néron model `𝒩'` over `𝓞_{L'}`, there is a group
model `𝒰` (the identity component `𝒩'⁰`) that is an open subgroup both of `𝒩'` and of a base
change `𝒱` of `𝒩₀` (namely `𝒱 = 𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'}`, with `𝒰 = 𝒩₀⁰ ×_{𝓞_{L₀}} 𝓞_{L'}`).
Consequence of SGA 7 IX Thm 3.6 (Grothendieck's semistable reduction theorem: `A_{L₀}` is
semistable for some finite `L₀`) and SGA 7 IX Prop./Cor. 3.3 (in the semistable case
`(𝒩_{L'})⁰ = (𝒩⁰)_{L'}`), with the openness of the identity component (SGA 3 VI_B 3.10) and
the compatibility of Néron models with localization (BLR §1.2); all locators UNVERIFIED. -/
def SemistableNeronIdentityComponent : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K),
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        ∃ 𝒰 𝒱 : GroupModel A L', IsBaseChangeOf 𝒱 𝒩₀ ∧ IsOpenSubgroupModel 𝒰 𝒩' ∧
          IsOpenSubgroupModel 𝒰 𝒱

/-! ## Glue (stated; to be proved by the project) -/

/-- **Glue H4a.** The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

/-- **Glue M6.** An open subgroup model has the same height: an open immersion `𝒰 → 𝒢` of group
schemes induces isomorphisms of the local rings along the unit section (so the same `ω`) and a
group bijection on complex points (on generic fibres it is an open immersion from a proper
connected scheme, hence an isomorphism; it need not be compatible with the two `gen`). -/
def OpenSubgroupHeight : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L), IsOpenSubgroupModel 𝒰 𝒢 → 𝒰.height = 𝒢.height

/-- **The compositum.** Two number fields `L, L₀` over a number field `K` embed `K`-linearly in a
common number field `L'`. Proved (inside `AlgebraicClosure K`). -/
theorem compositum (K : Type) [Field K] [NumberField K] (L L₀ : Type) [Field L] [NumberField L]
    [Algebra K L] [Field L₀] [NumberField L₀] [Algebra K L₀] :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra K L') (_ : Algebra L L')
      (_ : Algebra L₀ L'), IsScalarTower K L L' ∧ IsScalarTower K L₀ L' := by
  let Ω := AlgebraicClosure K
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite K L₀ := Module.Finite.of_restrictScalars_finite ℚ K L₀
  let eL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eL₀ : L₀ →ₐ[K] Ω := IsAlgClosed.lift
  let E : IntermediateField K Ω := eL.fieldRange ⊔ eL₀.fieldRange
  haveI : FiniteDimensional K eL.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL).toLinearEquiv
  haveI : FiniteDimensional K eL₀.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL₀).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  haveI : NumberField E := ⟨⟩
  let f : L →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField eL).toAlgHom
  let f₀ : L₀ →ₐ[K] E := (IntermediateField.inclusion le_sup_right).comp
    (AlgEquiv.ofInjectiveField eL₀).toAlgHom
  letI : Algebra L E := f.toRingHom.toAlgebra
  letI : Algebra L₀ E := f₀.toRingHom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  · exact IsScalarTower.of_algebraMap_eq fun x => (f₀.commutes x).symm


/-- **Glue (stated): an open immersion of group models does not increase the height.** If
`f : 𝒰 → 𝒢` is a homomorphism of group models of `A_L` whose underlying morphism is an open
immersion (so, by `genericIso_of_openImmersion`, an isomorphism on generic fibres), then
`h(𝒰) ≤ h(𝒢)`: the unit section of `𝒢` factors through `𝒰` (`e_𝒢 = e_𝒰 ≫ f`), `f` induces
isomorphisms of local rings along it, so `ω_𝒰 = ω_𝒢`; complex points correspond bijectively
(`pts_comp_bijective`). -/
def OpenImmersionHeightLe : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) (f : 𝒰.G ⟶ 𝒢.G), IsOpenImmersion f.left → IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒰.height ≤ 𝒢.height

/-- **Glue M6 from `HeightAntitone` and `OpenImmersionHeightLe`** (the generic-isomorphism
clause is proved, `genericIso_of_openImmersion`). -/
theorem openSubgroupHeight_of (hA : HeightAntitone) (hO : OpenImmersionHeightLe) :
    OpenSubgroupHeight := by
  intro K _ A L _ _ _ 𝒰 𝒢 ⟨f, hf, hm⟩
  haveI := hf
  have hi := genericIso_of_openImmersion 𝒰 𝒢 f
  exact le_antisymm (hO K A L 𝒰 𝒢 f hf hm hi) (hA K A L 𝒰 𝒢 f hm hi)

/-- **H5 in the form R19-R21 need**, from the leaves N1, N2 and the three remaining glue
statements (`NeronModelMinimal`, `GroupModelBaseChangeExists` and `OpenSubgroupHeight` of
h5-neron's version are now theorems or follow from these). Same conclusion as h5-neron's
`stableFaltingsHeight_eq_neron_all`. -/
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hA : HeightAntitone) (hO : OpenImmersionHeightLe)
    (hbc : ModelHeightBaseChange) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height := by
  have hmin := neronModelMinimal_of_heightAntitone hA
  have hbcE := groupModelBaseChangeExists
  have hop := openSubgroupHeight_of hA hO
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hbase⟩ := hN2 K A
  have heq : stableFaltingsHeight A = 𝒩₀.height := by
    rw [stableFaltingsHeight_eq_iInf_height]
    refine le_antisymm (iInf_le_of_le (FinExt.mk L₀) (iInf_le_of_le 𝒩₀ le_rfl)) ?_
    refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    obtain ⟨L', j1, j2, j3, j4, j5, t1, t2⟩ := compositum K E.L L₀
    obtain ⟨𝒢', h𝒢'⟩ := hbcE K A E.L L' 𝒢
    obtain ⟨𝒩', h𝒩'⟩ := hN1 K A L'
    obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
    calc 𝒩₀.height = 𝒱.height := (hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱).symm
      _ = 𝒰.height := (hop K A L' 𝒰 𝒱 h𝒰𝒱).symm
      _ = 𝒩'.height := hop K A L' 𝒰 𝒩' h𝒰𝒩
      _ ≤ 𝒢'.height := hmin K A L' 𝒩' 𝒢' h𝒩'
      _ = 𝒢.height := hbc K A E.L L' 𝒢 𝒢' h𝒢'
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, heq, ?_⟩
  intro L' j1 j2 j3 j4 j5 𝒩' h𝒩'
  obtain ⟨𝒰, 𝒱, h𝒱, h𝒰𝒩, h𝒰𝒱⟩ := hbase L' 𝒩' h𝒩'
  rw [heq, ← hbc K A L₀ L' 𝒩₀ 𝒱 h𝒱, ← hop K A L' 𝒰 𝒱 h𝒰𝒱, hop K A L' 𝒰 𝒩' h𝒰𝒩]

end Reduction

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.genBC_isMonHom
#print axioms ZInQ.H5Glue.groupModelBaseChangeExists
#print axioms ZInQ.H5Glue.isMonHom_of_map
#print axioms ZInQ.H5Glue.neron_lift_isMonHom
#print axioms ZInQ.H5Glue.neronModelMinimal_of_heightAntitone
#print axioms ZInQ.H5Glue.isOpenImmersion_pullback_map
#print axioms ZInQ.H5Glue.isIso_of_openImmersion_self
#print axioms ZInQ.H5Glue.genericIso_of_openImmersion
#print axioms ZInQ.H5Glue.pts_comp_bijective
#print axioms ZInQ.H5Glue.compositum
#print axioms ZInQ.H5Glue.openSubgroupHeight_of
#print axioms ZInQ.H5Glue.stableFaltingsHeight_eq_neron_all
