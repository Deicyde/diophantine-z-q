
/-! ## g0-heightadd (2026-11-13): additivity `h(A) + h(Z) ≤ h(A × Z)` (glue E4)

Everything above this line is copied verbatim from `scratch/g0-split/Split.lean` lines
16667-18603 (= `scratch/def-faltings/Faltings.lean`: the definitions of `ZInQ.DefFaltings`,
in particular its `AbVar`, `GroupModel`, `MetrizedModel`, `stableFaltingsHeight`,
`NeronModelMinimal`). Below: h5-neron's Néron-model glue (copied from
`scratch/h5-neron/H5Neron.lean`, parts A and E, with `PkgI3.AbVar` replaced by
`ZInQ.DefFaltings.AbVar`, i.e. the line `open PkgI3 (AbVar)` dropped), then the piece. -/

namespace ZInQ.H5Neron

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory

section General

variable {S S' : Scheme.{0}} (j : S' ⟶ S) (P : Over S → Prop)

/-- The Néron mapping property of `N` (over `S`) for `A` (over `S'`) along `j`, tested on the
objects satisfying `P`. -/
def NeronProp (N : Over S) (A : Over S') (e : (Over.pullback j).obj N ≅ A) : Prop :=
  ∀ Y : Over S, P Y → Function.Bijective fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom

variable {j P}

/-- Existence and uniqueness of the extension. -/
theorem NeronProp.lift {N : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) {Y : Over S} (hY : P Y) (g : (Over.pullback j).obj Y ⟶ A) :
    ∃! f : Y ⟶ N, (Over.pullback j).map f ≫ e.hom = g := by
  obtain ⟨f, hf⟩ := (h Y hY).2 g
  exact ⟨f, hf, fun f' hf' => (h Y hY).1 (hf'.trans hf.symm)⟩

/-- **Uniqueness of Néron models**: two Néron models of `A` (each a test object) are isomorphic,
compatibly with the identifications of their generic fibres. -/
theorem NeronProp.uniqueIso {N N' : Over S} {A : Over S'} {e : (Over.pullback j).obj N ≅ A}
    {e' : (Over.pullback j).obj N' ≅ A} (h : NeronProp j P N A e) (h' : NeronProp j P N' A e')
    (hN : P N) (hN' : P N') :
    ∃ φ : N ≅ N', (Over.pullback j).map φ.hom ≫ e'.hom = e.hom := by
  obtain ⟨f, hf⟩ := (h' N hN).2 e.hom
  obtain ⟨f', hf'⟩ := (h N' hN').2 e'.hom
  simp only at hf hf'
  have h1 : f ≫ f' = 𝟙 N := by
    apply (h N hN).1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  have h2 : f' ≫ f = 𝟙 N' := by
    apply (h' N' hN').1
    simp only [Functor.map_comp, Category.assoc, hf', hf]
    erw [(Over.pullback j).map_id, Category.id_comp]
  exact ⟨⟨f, f', h1, h2⟩, hf⟩

/-- The identification of the generic fibre of `N₁ ⊗ N₂` with `A₁ ⊗ A₂`. -/
noncomputable def tensorGen {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (Over.pullback j).obj (N₁ ⊗ N₂) ≅ A₁ ⊗ A₂ :=
  prodComparisonIso (Over.pullback j) N₁ N₂ ≪≫ tensorIso e₁ e₂

theorem tensorGen_fst {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ fst A₁ A₂ = (Over.pullback j).map (fst N₁ N₂) ≫ e₁.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_fst,
    CartesianMonoidalCategory.prodComparison_fst_assoc]

theorem tensorGen_snd {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    (e₁ : (Over.pullback j).obj N₁ ≅ A₁) (e₂ : (Over.pullback j).obj N₂ ≅ A₂) :
    (tensorGen e₁ e₂).hom ≫ snd A₁ A₂ = (Over.pullback j).map (snd N₁ N₂) ≫ e₂.hom := by
  rw [tensorGen, Iso.trans_hom, prodComparisonIso_hom, tensorIso_hom, Category.assoc, tensorHom_snd,
    CartesianMonoidalCategory.prodComparison_snd_assoc]

/-- **A product of Néron models is a Néron model of the product.** -/
theorem NeronProp.tensor {N₁ N₂ : Over S} {A₁ A₂ : Over S'}
    {e₁ : (Over.pullback j).obj N₁ ≅ A₁} {e₂ : (Over.pullback j).obj N₂ ≅ A₂}
    (h₁ : NeronProp j P N₁ A₁ e₁) (h₂ : NeronProp j P N₂ A₂ e₂) :
    NeronProp j P (N₁ ⊗ N₂) (A₁ ⊗ A₂) (tensorGen e₁ e₂) := by
  intro Y hY
  have hfst : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      fst A₁ A₂ = (Over.pullback j).map (f ≫ fst N₁ N₂) ≫ e₁.hom := by
    intro f
    rw [Category.assoc, tensorGen_fst, Functor.map_comp, Category.assoc]
  have hsnd : ∀ f : Y ⟶ N₁ ⊗ N₂, ((Over.pullback j).map f ≫ (tensorGen e₁ e₂).hom) ≫
      snd A₁ A₂ = (Over.pullback j).map (f ≫ snd N₁ N₂) ≫ e₂.hom := by
    intro f
    rw [Category.assoc, tensorGen_snd, Functor.map_comp, Category.assoc]
  constructor
  · intro f f' hff'
    have a := hfst f
    have b := hfst f'
    have c := hsnd f
    have d := hsnd f'
    simp only at hff'
    rw [hff'] at a c
    apply CartesianMonoidalCategory.hom_ext
    · exact (h₁ Y hY).1 (a.symm.trans b)
    · exact (h₂ Y hY).1 (c.symm.trans d)
  · intro g
    obtain ⟨f₁, hf₁⟩ := (h₁ Y hY).2 (g ≫ fst A₁ A₂)
    obtain ⟨f₂, hf₂⟩ := (h₂ Y hY).2 (g ≫ snd A₁ A₂)
    refine ⟨CartesianMonoidalCategory.lift f₁ f₂, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [hfst, CartesianMonoidalCategory.lift_fst]; exact hf₁
    · rw [hsnd, CartesianMonoidalCategory.lift_snd]; exact hf₂

end General

section GroupModels

open NumberField DefFaltings

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- The project's `IsNeronModel` is `NeronProp` for smooth test objects. -/
theorem GroupModel.isNeronModel_iff (𝒩 : GroupModel A L) :
    𝒩.IsNeronModel ↔ NeronProp (jL L) (fun Y => Smooth Y.hom) 𝒩.G (A.baseChange L).X 𝒩.gen :=
  ⟨fun h Y hY => @h Y hY, fun h Y hY => h Y hY⟩

/-- The comparison morphism `𝒢 → 𝒩` from any group model to a Néron model, compatible with the
identifications of the generic fibres with `A_L`, and unique with this property. -/
theorem GroupModel.IsNeronModel.lift {𝒩 : GroupModel A L} (h𝒩 : 𝒩.IsNeronModel)
    (𝒢 : GroupModel A L) :
    ∃! f : 𝒢.G ⟶ 𝒩.G, (Over.pullback (jL L)).map f ≫ 𝒩.gen.hom = 𝒢.gen.hom :=
  ((GroupModel.isNeronModel_iff 𝒩).mp h𝒩).lift (P := fun Y => Smooth Y.hom)
    (show Smooth 𝒢.G.hom from inferInstance) 𝒢.gen.hom

/-- Two Néron models of `A_L` are isomorphic over `𝓞_L`, compatibly with `gen`. -/
theorem GroupModel.IsNeronModel.uniqueIso {𝒩 𝒩' : GroupModel A L} (h : 𝒩.IsNeronModel)
    (h' : 𝒩'.IsNeronModel) :
    ∃ φ : 𝒩.G ≅ 𝒩'.G, (Over.pullback (jL L)).map φ.hom ≫ 𝒩'.gen.hom = 𝒩.gen.hom :=
  ((GroupModel.isNeronModel_iff 𝒩).mp h).uniqueIso ((GroupModel.isNeronModel_iff 𝒩').mp h')
    (show Smooth 𝒩.G.hom from inferInstance) (show Smooth 𝒩'.G.hom from inferInstance)

end GroupModels

/-! ## Transport along isomorphisms, and the additivity direction `h(A) + h(B) ≤ h(A × B)` -/

section Transport

variable {S S' : Scheme.{0}} {j : S' ⟶ S} {P : Over S → Prop}

/-- The Néron property is invariant under isomorphisms of `N` and of `A`. -/
theorem NeronProp.of_iso {N N' : Over S} {A A' : Over S'} {e : (Over.pullback j).obj N ≅ A}
    (h : NeronProp j P N A e) (φ : N' ≅ N) (ψ : A ≅ A') (e' : (Over.pullback j).obj N' ≅ A')
    (he : (Over.pullback j).map φ.hom ≫ e.hom ≫ ψ.hom = e'.hom) : NeronProp j P N' A' e' := by
  intro Y hY
  have key : (fun f : Y ⟶ N' => (Over.pullback j).map f ≫ e'.hom) =
      (fun g => g ≫ ψ.hom) ∘ (fun f : Y ⟶ N => (Over.pullback j).map f ≫ e.hom) ∘
        (fun f => f ≫ φ.hom) := by
    funext f
    simp only [Function.comp, Functor.map_comp, Category.assoc, ← he]
  rw [key]
  refine Function.Bijective.comp ?_ ((h Y hY).comp ?_)
  · exact ⟨fun a b hab => (cancel_mono ψ.hom).mp hab, fun c => ⟨c ≫ ψ.inv, by simp⟩⟩
  · exact ⟨fun a b hab => (cancel_mono φ.hom).mp hab, fun c => ⟨c ≫ φ.inv, by simp⟩⟩

end Transport

section Additivity

open NumberField DefFaltings

variable {K : Type} [Field K]

/-- `C ≅ A × B` as abelian varieties: an isomorphism `C ≅ A ⊗ B` of `K`-schemes whose two
components are homomorphisms. (Mathlib v4.35 cannot form `A × B` as an `AbVar`: it lacks the
stability of geometric integrality under composition; so the product enters as `C`.) -/
def IsProductAbVar (C A B : AbVar K) : Prop :=
  ∃ e : C.X ≅ A.X ⊗ B.X, IsMonHom (e.hom ≫ fst A.X B.X) ∧ IsMonHom (e.hom ≫ snd A.X B.X)

/-- `C_L ≅ A_L ⊗ B_L`. -/
noncomputable def bcProd {A B C : AbVar K} (L : Type) [Field L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) : (C.baseChange L).X ≅ (A.baseChange L).X ⊗ (B.baseChange L).X :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso eC ≪≫
    prodComparisonIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))) A.X B.X

/-- `𝒢P ≅ 𝒢₁ × 𝒢₂` as group models of `C_L ≅ A_L × B_L`. -/
def IsProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (eC : C.X ≅ A.X ⊗ B.X) (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) :
    Prop :=
  ∃ e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G, IsMonHom (e.hom ≫ fst _ _) ∧ IsMonHom (e.hom ≫ snd _ _) ∧
    (Over.pullback (jL L)).map e.hom ≫ (tensorGen 𝒢₁.gen 𝒢₂.gen).hom =
      𝒢P.gen.hom ≫ (bcProd L eC).hom

/-- **A product of Néron models is a Néron model** (for group models). -/
theorem isNeronModel_of_isProductModel {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
    [Algebra K L] {eC : C.X ≅ A.X ⊗ B.X} {𝒢P : GroupModel C L} {𝒩₁ : GroupModel A L}
    {𝒩₂ : GroupModel B L} (h₁ : 𝒩₁.IsNeronModel) (h₂ : 𝒩₂.IsNeronModel)
    (hP : IsProductModel eC 𝒢P 𝒩₁ 𝒩₂) : 𝒢P.IsNeronModel := by
  obtain ⟨e, -, -, he⟩ := hP
  rw [GroupModel.isNeronModel_iff] at h₁ h₂ ⊢
  refine (h₁.tensor h₂).of_iso e (bcProd L eC).symm 𝒢P.gen ?_
  rw [← Category.assoc, he]
  erw [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id]

/-- **Leaf N1 (Néron)**, as in `Reduction.lean` (BLR §1.4 Thm 3, UNVERIFIED locator). -/
def NeronModelExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L],
    ∃ 𝒩 : GroupModel A L, 𝒩.IsNeronModel

/-- **Glue P1.** Group models of `A_L` and `B_L` give a group model of `C_L ≅ A_L × B_L`
(the fibre product over `𝓞_L`; smooth, separated, quasi-compact; `GrpObj` of a product). -/
def ProductGroupModelExists : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X),
    IsMonHom (eC.hom ≫ fst A.X B.X) → IsMonHom (eC.hom ≫ snd A.X B.X) →
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] (𝒢₁ : GroupModel A L)
      (𝒢₂ : GroupModel B L), ∃ 𝒢P : GroupModel C L, IsProductModel eC 𝒢P 𝒢₁ 𝒢₂

/-- **Glue P2** (the direction used). The height of a product model is at least the sum of the
heights: `ω_{𝒢₁×𝒢₂} = ω_{𝒢₁} ⊕ ω_{𝒢₂}`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, the Arakelov degree is
additive, and a product of uniformizations is a uniformization of the product (equality holds). -/
def ProductModelHeight : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ → 𝒢₁.height + 𝒢₂.height ≤ 𝒢P.height

/-- **`h(A) + h(B) ≤ h(A × B)`** (rv-blueprints F1, the direction step E4 uses) from Néron
existence, Néron minimality and the two product glue statements. No semistable reduction is
needed: the comparison is made over each `L` separately. -/
theorem stableFaltingsHeight_add_le (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hP : ProductGroupModelExists) (hH : ProductModelHeight) (A B C : AbVar K)
    (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C := by
  obtain ⟨eC, h1, h2⟩ := hC
  rw [stableFaltingsHeight_eq_iInf_height C]
  refine le_iInf fun E => le_iInf fun 𝒢 => ?_
  obtain ⟨𝒩₁, hN₁⟩ := hN1 K A E.L
  obtain ⟨𝒩₂, hN₂⟩ := hN1 K B E.L
  obtain ⟨𝒢P, h𝒢P⟩ := hP K A B C eC h1 h2 E.L 𝒩₁ 𝒩₂
  have hA : stableFaltingsHeight A ≤ 𝒩₁.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₁ le_rfl)
  have hB : stableFaltingsHeight B ≤ 𝒩₂.height := by
    rw [stableFaltingsHeight_eq_iInf_height]; exact iInf_le_of_le E (iInf_le_of_le 𝒩₂ le_rfl)
  calc stableFaltingsHeight A + stableFaltingsHeight B ≤ 𝒩₁.height + 𝒩₂.height :=
        add_le_add hA hB
    _ ≤ 𝒢P.height := hH K A B C eC E.L 𝒢P 𝒩₁ 𝒩₂ h𝒢P
    _ ≤ 𝒢.height :=
        hmin K C E.L 𝒢P 𝒢 (isNeronModel_of_isProductModel hN₁ hN₂ h𝒢P)

end Additivity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open scoped TensorProduct

/-! ## Part E: the glue `ProductGroupModelExists`, proved; additivity from three hypotheses -/

section ProductProof

open scoped Obj

/-- `prodComparison` of a braided monoidal functor between cartesian categories is a monoid
morphism. -/
theorem isMonHom_prodComparisonIso {S S' : Scheme.{0}} (j : S' ⟶ S) (X Y : Over S) [GrpObj X]
    [GrpObj Y] :
    IsMonHom (prodComparisonIso (Over.pullback j) X Y).hom := by
  have h : (prodComparisonIso (Over.pullback j) X Y).hom =
      (Functor.Monoidal.μIso (Over.pullback j) X Y).inv := by
    rw [prodComparisonIso_hom, ← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    rfl
  have h0 : IsMonHom (Functor.Monoidal.μIso (Over.pullback j) X Y).hom :=
    (inferInstance : IsMonHom (Functor.LaxMonoidal.μ (Over.pullback j) X Y))
  rw [h]
  infer_instance

/-- **Glue P1, proved.** -/
theorem productGroupModelExists : ProductGroupModelExists := by
  unfold ProductGroupModelExists
  intro K _ A B C eC h1 h2 L _ _ _ 𝒢₁ 𝒢₂
  haveI : Smooth (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show Smooth (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsSeparated (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show IsSeparated (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : QuasiCompact (𝒢₁.G ⊗ 𝒢₂.G).hom := by
    show QuasiCompact (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom ≫ 𝒢₁.G.hom); infer_instance
  haveI : IsMonHom eC.hom := by
    have : eC.hom = lift (eC.hom ≫ fst A.X B.X) (eC.hom ≫ snd A.X B.X) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp
    rw [this]; infer_instance
  let F := Over.pullback (jL L)
  let F' := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  let gen : genericFibre L (𝒢₁.G ⊗ 𝒢₂.G) ≅ (C.baseChange L).X :=
    tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm
  have gen_hom : letI : GrpObj (genericFibre L (𝒢₁.G ⊗ 𝒢₂.G)) := Functor.grpObjObj
      IsMonHom gen.hom := by
    let g₁ : F.obj 𝒢₁.G ⟶ F'.obj A.X := 𝒢₁.gen.hom
    let g₂ : F.obj 𝒢₂.G ⟶ F'.obj B.X := 𝒢₂.gen.hom
    have g1 : IsMonHom g₁ := 𝒢₁.gen_hom
    have g2 : IsMonHom g₂ := 𝒢₂.gen_hom
    have p1 := isMonHom_prodComparisonIso (jL L) 𝒢₁.G 𝒢₂.G
    have p2 := isMonHom_prodComparisonIso (Spec.map (CommRingCat.ofHom (algebraMap K L))) A.X B.X
    have : IsMonHom ((prodComparisonIso F 𝒢₁.G 𝒢₂.G).hom ≫
        (g₁ ⊗ₘ g₂) ≫
        (prodComparisonIso F' A.X B.X).inv ≫ F'.map eC.inv) := inferInstance
    exact this
  refine ⟨⟨𝒢₁.G ⊗ 𝒢₂.G, gen, gen_hom⟩, Iso.refl _, ?_, ?_, ?_⟩
  · show IsMonHom (𝟙 _ ≫ fst _ _); infer_instance
  · show IsMonHom (𝟙 _ ≫ snd _ _); infer_instance
  · show F.map (𝟙 _) ≫ _ = (tensorGen 𝒢₁.gen 𝒢₂.gen ≪≫ (bcProd L eC).symm).hom ≫ _
    rw [F.map_id, Category.id_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]


/-- **`h(A) + h(B) ≤ h(A × B)` from N1, `NeronModelMinimal` and `ProductModelHeight` only.** -/
theorem stableFaltingsHeight_add_le' (hN1 : NeronModelExists) (hmin : NeronModelMinimal)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : AbVar K) (hC : IsProductAbVar C A B) :
    stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C :=
  stableFaltingsHeight_add_le hN1 hmin productGroupModelExists hH A B C hC

end ProductProof

end ZInQ.H5Neron

/-! ## The leaf bundle field used: `LeafAdopt.H5` (copied verbatim from `Split.lean` l. 18755-18768;
it is the field `h5` of `HSyn.ResearchLeaves`) -/

namespace LeafAdopt

/-- **H5 (rv-blueprints F2): the stable Faltings height is the published one, as an explicit
leaf.** `StableHeightFinite` (over a number field, `stableFaltingsHeight A ∈ ℝ`) and
`NeronModelMinimal` (over each `L`, a group model with the Néron mapping property has the least
height). Each of R18-R22 is a consequence of its publication only together with H5
(rv-blueprints §1.2), and the direction `h(A) + h(Z) ≤ h(A × Z)` of additivity that E4 uses needs
Néron models and H5 (F1). *Published*: Faltings 1983 §1; Deligne, Sém. Bourbaki 616 (1983);
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990) 1.2/1, 1.4/3; SGA 7 I, Exp. IX 3.3, 3.6
(locators UNVERIFIED). **Caveat**: `StableHeightFinite` holds for def-faltings' infimum only if
its index set is nonempty, which is what the open Props `AnalyticUniformizationExists` and
`HodgeLatticeTheorem` (with `AnalyticUniformizationUnique` for independence of the
uniformization) assert; they are true theorems (Mumford §1 with GAGA; smoothness of `𝒢`) but
unproved in Lean. So H5 as stated is "published theorem + correctness of the definition". -/
def H5 : Prop :=
  ZInQ.DefFaltings.StableHeightFinite ∧ ZInQ.DefFaltings.NeronModelMinimal

end LeafAdopt

noncomputable section

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.DefFaltings

/-! ### The piece, copied verbatim from `Split.lean` (l. 19461-19465 and 19553-19559) -/

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- **Missing piece 5 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-! ### g0-heightadd: the proof -/

/-- **Bridge (glue, proved).** g0-split's `IsProductOf` gives h5-neron's `IsProductAbVar`
(the isomorphism is `lift p₁ p₂`, whose components are `p₁`, `p₂`). -/
theorem isProductAbVar_of_isProductOf {K : Type} [Field K] {P A Z : ZInQ.DefFaltings.AbVar K}
    (h : IsProductOf P.X A.X Z.X) : H5Neron.IsProductAbVar P A Z := by
  obtain ⟨p₁, p₂, h₁, h₂, hI⟩ := h
  refine ⟨asIso (lift p₁ p₂), ?_, ?_⟩
  · rw [asIso_hom, lift_fst]; exact h₁
  · rw [asIso_hom, lift_snd]; exact h₂

/-- **`HeightAdditivity` from Néron existence (leaf N1), the bundle field `h5` and the product
height glue P2** (h5-neron's `stableFaltingsHeight_add_le'` plus the bridge and the passage from
`EReal` to `ℝ`). -/
theorem heightAdditivity_of (hN1 : H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hH : H5Neron.ProductModelHeight) : HeightAdditivity := by
  intro L _ _ P A Z hP a z p ha hz hp
  have key := H5Neron.stableFaltingsHeight_add_le' hN1 h5.2 hH A Z P
    (isProductAbVar_of_isProductOf hP)
  rw [ha, hz, hp, ← EReal.coe_add, EReal.coe_le_coe_iff] at key
  exact key

end G0Split

end HSyn

end

#print axioms HSyn.G0Split.isProductAbVar_of_isProductOf
#print axioms HSyn.G0Split.heightAdditivity_of
#print axioms ZInQ.H5Neron.productGroupModelExists
