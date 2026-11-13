section H5NeronSec
/-! ### leaf-adopt3 fold (2026-11-13): task h5-neron

Copied from `scratch/h5-neron/H5Neron.lean` (compiled there against the kernel module
`ZInQKernel.HDecomp.Faltings.Leaves`). Changes: the `import` line and the `#print axioms` lines are
dropped; the four lines `open PkgI3 (AbVar)` are deleted (in this file `open DefFaltings` already
brings def-faltings' copy `ZInQ.DefFaltings.AbVar`, and keeping both would make `AbVar` ambiguous);
`AbVar.zero` (= `PkgI3.AbVar.zero` in the kernel) is restated for the copy as
`ZInQ.H5Neron.AbVar.zero`, just before `section ZeroAV`. The bridges at the end are new. All
`ZInQ.DefFaltings` declarations used (`GroupModel`, `IsNeronModel`, `height`, `MetrizedModel`,
`stableFaltingsHeight_eq_iInf_height`, `NeronModelMinimal`, `StableHeightFinite`, `isogDeg`,
`ptObj`, `grKappa`, ...) are textually identical in section `DefFaltingsSec` above. -/

/-! # h5-neron: Néron models and the stable Faltings height (node H5), combined file

Self-contained combination of `Neron.lean` (part A), `ZeroAV.lean` (part B) and
`Reduction.lean` (part C) of `scratch/h5-neron/`, with part D (the leaves and glue for the zero
abelian variety). Mathlib + project only; no unproved step, no `axiom`. See `docs/research/h5-neron.md`. -/

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

/-- Maps into an object isomorphic to the unit are equal. -/
theorem hom_ext_of_iso_unit {C : Type*} [Category C] [CartesianMonoidalCategory C] {X Y : C}
    (i : X ≅ 𝟙_ C) (f g : Y ⟶ X) : f = g := by
  rw [← cancel_mono i.hom]; exact toUnit_unique _ _

section DimZero

variable {L : Type} [Field L] [NumberField L] {K : Type} [Field K] [Algebra K L] {A : AbVar K}

/-- `⋀^0 ω ≅ L`. -/
noncomputable def hodgeZeroEquiv (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 ≃ₗ[L] L :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (exteriorPower.zeroEquiv (𝓞 L) 𝒢.cotangent) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid (𝓞 L) L L

/-- The empty wedge `1 ⊗ 1 ∈ ⋀^0`. -/
noncomputable def wedge0 (𝒢 : GroupModel A L) : 𝒢.hodgeSpace 0 :=
  (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) 0 (fun i : Fin 0 => (i.elim0 : 𝒢.cotangent))

theorem hodgeZeroEquiv_wedge0 (𝒢 : GroupModel A L) : hodgeZeroEquiv 𝒢 (wedge0 𝒢) = 1 := by
  simp [hodgeZeroEquiv, wedge0]

theorem wedge0_ne_zero (𝒢 : GroupModel A L) : wedge0 𝒢 ≠ 0 := by
  intro h
  have := congrArg (hodgeZeroEquiv 𝒢) h
  rw [hodgeZeroEquiv_wedge0, LinearEquiv.map_zero] at this
  exact one_ne_zero this

theorem wedge_eq_wedge0 (𝒢 : GroupModel A L) (f : Fin 0 → IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.wedge f = wedge0 𝒢 := by
  unfold GroupModel.wedge wedge0
  congr 2
  funext i
  exact i.elim0

theorem detLattice_zero (𝒢 : GroupModel A L) :
    𝒢.detLattice 0 = Submodule.span (𝓞 L) {wedge0 𝒢} := by
  unfold GroupModel.detLattice
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, rfl⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0
  · rintro rfl
    refine ⟨fun i => i.elim0, ?_⟩
    unfold wedge0
    congr 2
    funext i
    exact i.elim0

/-- The covolume of the (only) lattice in `ℂ⁰` is `1`. -/
theorem covolume_fin_zero (Λ : Submodule ℤ (Fin 0 → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ZLattice.covolume Λ = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ volume (F := Set.univ)
    (IsAddFundamentalDomain.mk' nullMeasurableSet_univ fun x =>
      ⟨0, Set.mem_univ _, fun y _ => Subsingleton.elim _ _⟩)]
  simp [Measure.real, volume_pi]

/-- **Every metrized model of dimension `0` has height `0`** (for every `A`). -/
theorem modelHeight_dim_zero (M : MetrizedModel A L 0) : M.hodge.modelHeight = 0 := by
  have hs : M.hodge.lattice = Submodule.span (𝓞 L) {wedge0 M.model} :=
    M.lattice_eq.trans (detLattice_zero _)
  rw [M.hodge.modelHeight_of_span hs (wedge0_ne_zero _)]
  have hc : ∀ τ, M.hodge.coeff τ (wedge0 M.model) = 1 := by
    intro τ
    obtain ⟨Φ, -, hΦ⟩ := M.arch τ
    have := hΦ (fun i => i.elim0)
    rw [wedge_eq_wedge0] at this
    rw [this]
    simp [GroupModel.jacDet]
  have hcov : ∀ τ, torusMetricSq (M.hodge.periods τ) 1 = 1 := by
    intro τ
    have := M.hodge.periods_discrete τ
    have := M.hodge.periods_isZLattice τ
    simp [torusMetricSq, covolume_fin_zero]
  simp [hc, hcov]

end DimZero

/-- (leaf-adopt3 fold) The zero abelian variety `Spec K`, for def-faltings' copy
`ZInQ.DefFaltings.AbVar`: the body of `PkgI3.AbVar.zero` (`ZInQKernel/HDecomp/Objects.lean`, also in
this file in section `PkgI3`) verbatim. In the kernel the source file used `PkgI3.AbVar.zero`
(there `ZInQ.DefFaltings` works over `PkgI3.AbVar`); here `GroupModel` needs the copy. Inside
`namespace ZInQ.H5Neron` the name `AbVar.zero` resolves to this declaration. -/
noncomputable def AbVar.zero (K : Type) [Field K] : ZInQ.DefFaltings.AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

section ZeroAV

variable (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-- `((Spec K)_L) ≅ 𝟙`. -/
noncomputable def bcUnitIso : ((AbVar.zero K).baseChange L).X ≅ 𝟙_ _ :=
  (Functor.Monoidal.εIso (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))).symm

/-- The trivial group model `Spec 𝓞_L` of `(Spec K)_L`. -/
noncomputable def trivModel : GroupModel (AbVar.zero K) L where
  G := 𝟙_ _
  smooth := by dsimp; infer_instance
  separated := by dsimp; infer_instance
  qc := by dsimp; infer_instance
  gen := (Functor.Monoidal.εIso (Over.pullback (jL L))).symm ≪≫ (bcUnitIso K L).symm
  gen_hom := by
    letI : GrpObj (genericFibre L (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))))) :=
      Functor.grpObjObj
    exact ⟨hom_ext_of_iso_unit (bcUnitIso K L) _ _, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩

/-- `Spec 𝓞_L` is a Néron model of `(Spec K)_L`. -/
theorem trivModel_isNeronModel : (trivModel K L).IsNeronModel := by
  intro Y _
  refine ⟨fun f g _ => toUnit_unique _ _, fun g => ⟨toUnit Y, hom_ext_of_iso_unit (bcUnitIso K L) _ _⟩⟩

/-- A group model of `(Spec K)_L` has exactly one complex point at each `τ`: `𝒢(ℂ)_τ` injects
into `(Spec K)_L(ℂ)_τ` (adjunction `Over.map ⊣ Over.pullback`), which is a point. -/
theorem pts_subsingleton (𝒢 : GroupModel (AbVar.zero K) L) (τ : L →+* ℂ) :
    Subsingleton (𝒢.Pts τ) := by
  constructor
  intro p q
  let P' : Over (Spec (CommRingCat.of L)) := Over.mk (Spec.map (CommRingCat.ofHom τ))
  let e : GroupModel.ptC τ ≅ (Over.map (jL L)).obj P' := Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, P', jL, Over.map_obj_hom, Over.mk_hom, Iso.refl_hom,
      Category.id_comp, ← Spec.map_comp]
    rfl)
  let adj := Over.mapPullbackAdj (jL L)
  rw [← cancel_epi e.inv]
  apply (adj.homEquiv P' 𝒢.G).injective
  have := hom_ext_of_iso_unit (bcUnitIso K L) ((adj.homEquiv P' 𝒢.G) (e.inv ≫ p) ≫ 𝒢.gen.hom)
    ((adj.homEquiv P' 𝒢.G) (e.inv ≫ q) ≫ 𝒢.gen.hom)
  exact (cancel_mono 𝒢.gen.hom).mp this

/-- The zero abelian variety has no metrized model of dimension `g ≥ 1`: the kernel of a
uniformization `ℂ^g → 𝒢(ℂ)_τ = {pt}` would be all of `ℂ^g`, which is not discrete. -/
theorem no_metrized_succ (n : ℕ) (M : MetrizedModel (AbVar.zero K) L (n + 1)) : False := by
  haveI : Algebra.IsAlgebraic ℚ L := inferInstance
  let τ : L →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := L)).toRingHom
  obtain ⟨Φ, hΦ, -⟩ := M.arch τ
  have hall : ∀ z, z ∈ M.hodge.periods τ := fun z => by
    have := pts_subsingleton K L M.model τ
    exact (hΦ.2.1 z).mp (Subsingleton.elim _ _)
  have := M.hodge.periods_discrete τ
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)))
  have h0 : (0 : Fin (n + 1) → ℂ) ∈ t := by
    have : (⟨0, hall 0⟩ : M.hodge.periods τ) ∈ Subtype.val ⁻¹' t := by
      rw [hpre]; exact Set.mem_singleton _
    exact this
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  let y : Fin (n + 1) → ℂ := fun _ => ((ε / 2 : ℝ) : ℂ)
  have hy : y ∈ t := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have : (⟨y, hall y⟩ : M.hodge.periods τ) ∈ ({⟨0, hall 0⟩} : Set (M.hodge.periods τ)) := by
    rw [← hpre]; exact hy
  have hy0 : y = 0 := congrArg Subtype.val (Set.mem_singleton_iff.mp this)
  have := congrFun hy0 0
  simp only [y, Pi.zero_apply, Complex.ofReal_eq_zero] at this
  linarith

/-- `τ` as a `τ`-semilinear map `L → ℂ`. -/
noncomputable def semσ (σ : L →+* ℂ) : L →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a x := map_mul σ a x

/-- The Hodge data of a group model in dimension `0`. -/
noncomputable def trivHodge (𝒢 : GroupModel (AbVar.zero K) L) : HodgeData L 0 (𝒢.hodgeSpace 0) where
  lattice := 𝒢.detLattice 0
  finrank_eq_one := by rw [(hodgeZeroEquiv 𝒢).finrank_eq, Module.finrank_self]
  isLattice := ⟨wedge0 𝒢, by rw [detLattice_zero]; exact Submodule.mem_span_singleton_self _,
    wedge0_ne_zero 𝒢, by
      rw [detLattice_zero]; unfold secIndex; rw [AddSubgroup.relIndex_self]; norm_num⟩
  periods _ := ⊤
  periods_discrete _ := inferInstance
  periods_isZLattice _ := ⟨eq_top_iff.mpr fun x _ => by
    rw [Subsingleton.elim x 0]; exact zero_mem _⟩
  coeff σ := (semσ L σ).comp (hodgeZeroEquiv 𝒢).toLinearMap
  coeff_ne_zero σ h := by
    have := LinearMap.congr_fun h (wedge0 𝒢)
    simp [semσ, hodgeZeroEquiv_wedge0] at this

/-- The metrized trivial model. -/
noncomputable def trivMetrized : MetrizedModel (AbVar.zero K) L 0 where
  model := trivModel K L
  hodge := trivHodge K L (trivModel K L)
  lattice_eq := rfl
  arch τ := ⟨fun _ => toUnit _,
    ⟨fun _ _ => toUnit_unique _ _, fun z => ⟨fun _ => Submodule.mem_top, fun _ => toUnit_unique _ _⟩,
      fun p => ⟨0, toUnit_unique _ _⟩,
      fun U => by
        rcases Set.eq_empty_or_nonempty ((trivModel K L).dom (fun _ => toUnit _) U) with h | ⟨x, hx⟩
        · rw [h]; exact isOpen_empty
        · have : (trivModel K L).dom (fun _ => toUnit _) U = Set.univ :=
            Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
          rw [this]; exact isOpen_univ,
      fun U s => differentiableOn_const _⟩,
    fun f => by
      show semσ L τ (hodgeZeroEquiv _ ((trivModel K L).wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]⟩

/-- **The stable Faltings height of the zero abelian variety is `0`.** -/
theorem stableFaltingsHeight_zero [NumberField K] : stableFaltingsHeight (AbVar.zero K) = 0 := by
  refine le_antisymm ?_ ?_
  · have := stableFaltingsHeight_le (AbVar.zero K) (trivMetrized K K)
    rwa [modelHeight_dim_zero, EReal.coe_zero] at this
  · refine le_stableFaltingsHeight _ fun E g M => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K E.L n M).elim

/-- Every group model of `(Spec K)_L` has a metrized model of dimension `0`. -/
noncomputable def metrizedOf (𝒢 : GroupModel (AbVar.zero K) L) :
    MetrizedModel (AbVar.zero K) L 0 where
  model := 𝒢
  hodge := trivHodge K L 𝒢
  lattice_eq := rfl
  arch τ := by
    have hs := pts_subsingleton K L 𝒢 τ
    refine ⟨fun _ => 1, ⟨fun _ _ => Subsingleton.elim _ _,
      fun z => ⟨fun _ => Submodule.mem_top, fun _ => rfl⟩,
      fun p => ⟨0, Subsingleton.elim _ _⟩, fun U => ?_, fun U s => differentiableOn_const _⟩,
      fun f => ?_⟩
    · rcases Set.eq_empty_or_nonempty (𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U) with h | ⟨x, hx⟩
      · rw [h]; exact isOpen_empty
      · have : 𝒢.dom (fun _ => (1 : 𝒢.Pts τ)) U = Set.univ :=
          Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
        rw [this]; exact isOpen_univ
    · show semσ L τ (hodgeZeroEquiv _ (𝒢.wedge f)) = _
      rw [wedge_eq_wedge0, hodgeZeroEquiv_wedge0]
      simp [semσ, GroupModel.jacDet]

/-- **Every group model of the zero abelian variety has height `0`.** -/
theorem groupModel_height_zero (𝒢 : GroupModel (AbVar.zero K) L) : 𝒢.height = 0 := by
  refine le_antisymm ?_ ?_
  · refine iInf_le_of_le 0 (iInf_le_of_le (metrizedOf K L 𝒢) (iInf_le_of_le rfl ?_))
    rw [modelHeight_dim_zero, EReal.coe_zero]
  · refine le_iInf fun g => le_iInf fun M => le_iInf fun _ => ?_
    cases g with
    | zero => rw [modelHeight_dim_zero, EReal.coe_zero]
    | succ n => exact (no_metrized_succ K L n M).elim

/-- **`NeronModelMinimal` holds for the zero abelian variety.** -/
theorem neronModelMinimal_zero (𝒩 𝒢 : GroupModel (AbVar.zero K) L) (_ : 𝒩.IsNeronModel) :
    𝒩.height ≤ 𝒢.height := by
  rw [groupModel_height_zero, groupModel_height_zero]

/-- **`StableHeightFinite` holds for the zero abelian variety.** -/
theorem stableHeightFinite_zero [NumberField K] :
    stableFaltingsHeight (AbVar.zero K) ≠ ⊤ ∧ stableFaltingsHeight (AbVar.zero K) ≠ ⊥ := by
  rw [stableFaltingsHeight_zero]; exact ⟨EReal.zero_ne_top, EReal.zero_ne_bot⟩

/-- The identity of `Spec K` is an isogeny (so the hypothesis of R19 is satisfiable). -/
theorem isIsogeny_id_zero : IsIsogeny (𝟙 (AbVar.zero K).X) :=
  ⟨inferInstance, by rw [Over.id_left]; infer_instance, by rw [Over.id_left]; infer_instance⟩

/-- Every endomorphism of the zero abelian variety has degree `≤ 1`. -/
theorem isogDeg_zero_le_one (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) : isogDeg φ ≤ 1 := by
  unfold isogDeg
  have : Subsingleton {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1} :=
    ⟨fun a b => Subtype.ext (toUnit_unique _ _)⟩
  rcases isEmpty_or_nonempty {P : ptObj K (AlgebraicClosure K) ⟶ (AbVar.zero K).X // P ≫ φ = 1}
    with h | h
  · rw [Nat.card_of_isEmpty]; exact zero_le_one
  · rw [Nat.card_of_subsingleton h.some]

/-- **R21 for the zero abelian variety** (for every `g`, not only `g = dim`). -/
theorem R21_zero [NumberField K] (g : ℕ) :
    ((-(3 / 2) * g : ℝ) : EReal) ≤ stableFaltingsHeight (AbVar.zero K) := by
  rw [stableFaltingsHeight_zero]
  exact_mod_cast (by nlinarith [(Nat.cast_nonneg g : (0 : ℝ) ≤ g)] : -(3 / 2) * (g : ℝ) ≤ 0)

/-- **R20 for the zero abelian variety.** -/
theorem R20_zero [NumberField K] (φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X) (x y : ℝ)
    (hx : stableFaltingsHeight (AbVar.zero K) = x) (hy : stableFaltingsHeight (AbVar.zero K) = y) :
    |x - y| ≤ (1 / 2) * Real.log (isogDeg φ) := by
  rw [stableFaltingsHeight_zero] at hx hy
  have hx' : x = 0 := by exact_mod_cast hx.symm
  have hy' : y = 0 := by exact_mod_cast hy.symm
  rw [hx', hy', sub_zero, abs_zero]
  have := Real.log_natCast_nonneg (isogDeg φ)
  linarith

theorem one_le_grKappa (g d : ℕ) (hd : 1 ≤ d) (x : ℝ) : 1 ≤ grKappa g d x := by
  unfold grKappa
  apply one_le_pow₀
  have hm : 1 ≤ (max (max x (Real.log d)) 1) ^ 2 := one_le_pow₀ (le_max_right _ _)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ (14 * g : ℝ) ^ (64 * g ^ 2) := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · apply one_le_pow₀
      have : (1 : ℝ) ≤ g := by exact_mod_cast hg
      linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

/-- **R19 for the zero abelian variety** (for every `g`). -/
theorem R19_zero [NumberField K] (g : ℕ) (x : ℝ) (_ : stableFaltingsHeight (AbVar.zero K) = x)
    (h : ∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ) :
    (∃ φ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny φ ∧
        (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
      (∃ ψ : (AbVar.zero K).X ⟶ (AbVar.zero K).X, IsIsogeny ψ ∧
        (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) := by
  obtain ⟨φ, hφ⟩ := h
  have hb : (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x :=
    le_trans (by exact_mod_cast isogDeg_zero_le_one K φ)
      (one_le_grKappa g _ Module.finrank_pos x)
  exact ⟨⟨φ, hφ, hb⟩, ⟨φ, hφ, hb⟩⟩

end ZeroAV



open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Defs

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒢'` (over `𝓞_{L'}`) is the base change of `𝒢` (over `𝓞_L`) along `𝓞_L → 𝓞_{L'}`, as a group
scheme: an isomorphism of group objects `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. (The identifications with
`A_{L'}` are not compared; the height does not use them.) -/
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

/-- `𝒰 → 𝒢` is an open immersion of group schemes over `𝓞_L`. -/
def IsOpenSubgroupModel {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L) : Prop :=
  ∃ f : 𝒰.G ⟶ 𝒢.G, IsOpenImmersion f.left ∧ IsMonHom f

end Defs

/-! ## Leaves -/

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

/-- **Glue H4b.** A group model base-changes to a group model (smoothness, separatedness and
quasi-compactness are stable under base change; the group structure is transported by the monoidal
functor `Over.pullback`; the generic fibre is `A_L ×_L L' ≅ A_{L'}` by pullback pasting). -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

/-- **Glue M6.** An open subgroup model has the same height: an open immersion `𝒰 → 𝒢` of group
schemes induces isomorphisms of the local rings along the unit section (so the same `ω`) and a
group bijection on complex points (on generic fibres it is an open immersion from a proper
connected scheme, hence an isomorphism; it need not be compatible with the two `gen`). -/
def OpenSubgroupHeight : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒰 𝒢 : GroupModel A L), IsOpenSubgroupModel 𝒰 𝒢 → 𝒰.height = 𝒢.height

/-! ## Glue (proved): composita -/

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

/-! ## The reduction (proved) -/

/-- **H5 from the leaves N1, N2 and the glue.** For every abelian variety over a number field
there are a finite extension `L₀` and a Néron model `𝒩₀` over `𝓞_{L₀}` whose height is the stable
Faltings height. -/
theorem stableFaltingsHeight_eq_neron (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hmin : NeronModelMinimal)
    (hbc : ModelHeightBaseChange) (hbcE : GroupModelBaseChangeExists)
    (hop : OpenSubgroupHeight) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height := by
  obtain ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, hbase⟩ := hN2 K A
  refine ⟨L₀, i1, i2, i3, 𝒩₀, h𝒩₀, ?_⟩
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

/-- **H5, the form R19-R21 need.** Under the same hypotheses, with `L₀` and `𝒩₀` given by N2 (the
intended witness is a field of semistable reduction, where `𝒩₀.height` is Faltings' published
stable height; the Lean statement does not record semistability): the stable height equals
the Néron-model height over `L₀` and over **every** finite extension `L'` of `L₀`. -/
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hmin : NeronModelMinimal)
    (hbc : ModelHeightBaseChange) (hbcE : GroupModelBaseChangeExists)
    (hop : OpenSubgroupHeight) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀) (𝒩₀ : GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel →
        stableFaltingsHeight A = 𝒩'.height := by
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


/-! ## Part D: the leaves N1, N2 and the glue hold for the zero abelian variety (proved)

So the hypotheses of `stableFaltingsHeight_eq_neron` and `stableFaltingsHeight_add_le` are
consistent with the definitions in the only case Mathlib can construct. -/

section ZeroInstances

/-- A morphism into a monoid object isomorphic to the unit is a monoid morphism (instance
arguments are unified, not synthesized). -/
theorem isMonHom_of_iso_unit {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N : C}
    {_ : MonObj M} {_ : MonObj N} (i : N ≅ 𝟙_ C) (f : M ⟶ N) : IsMonHom f :=
  ⟨hom_ext_of_iso_unit i _ _, hom_ext_of_iso_unit i _ _⟩

/-- A Néron model of `(Spec K)_L` is isomorphic to the unit `Spec 𝓞_L`. -/
theorem neron_zero_iso_unit (K : Type) [Field K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel (AbVar.zero K) L) (h : 𝒩.IsNeronModel) : Nonempty (𝒩.G ≅ 𝟙_ _) := by
  obtain ⟨φ, -⟩ := GroupModel.IsNeronModel.uniqueIso h (trivModel_isNeronModel K L)
  exact ⟨φ⟩

/-- **N1 for the zero abelian variety.** -/
theorem neronModelExists_zero (K : Type) [Field K] (L : Type) [Field L] [NumberField L]
    [Algebra K L] : ∃ 𝒩 : GroupModel (AbVar.zero K) L, 𝒩.IsNeronModel :=
  ⟨trivModel K L, trivModel_isNeronModel K L⟩

/-- **N2 for the zero abelian variety** (with `L₀ = K`, `𝒩₀ = Spec 𝓞_K`). -/
theorem semistableNeronIdentityComponent_zero (K : Type) [Field K] [NumberField K] :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀)
      (𝒩₀ : GroupModel (AbVar.zero K) L₀),
      𝒩₀.IsNeronModel ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : GroupModel (AbVar.zero K) L'), 𝒩'.IsNeronModel →
        ∃ 𝒰 𝒱 : GroupModel (AbVar.zero K) L', IsBaseChangeOf 𝒱 𝒩₀ ∧
          IsOpenSubgroupModel 𝒰 𝒩' ∧ IsOpenSubgroupModel 𝒰 𝒱 := by
  refine ⟨K, inferInstance, inferInstance, inferInstance, trivModel K K,
    trivModel_isNeronModel K K, ?_⟩
  intro L' i1 i2 i3 i4 i5 𝒩' h𝒩'
  letI : Algebra K L' := i3
  obtain ⟨i⟩ := neron_zero_iso_unit K L' 𝒩' h𝒩'
  refine ⟨trivModel K L', trivModel K L', ?_, ?_, ?_⟩
  · unfold IsBaseChangeOf
    exact ⟨Functor.Monoidal.εIso _, isMonHom_of_iso_unit (Functor.Monoidal.εIso _).symm _⟩
  · refine ⟨i.inv, ?_, ⟨hom_ext_of_iso_unit i _ _, hom_ext_of_iso_unit i _ _⟩⟩
    show IsOpenImmersion ((Over.forget _).map i.inv)
    infer_instance
  · refine ⟨𝟙 _, ?_, inferInstance⟩
    rw [Over.id_left]; infer_instance

/-- **The glue statements hold for the zero abelian variety** (all its group models have height
`0`, `groupModel_height_zero`). -/
theorem glue_zero (K : Type) [Field K] (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] :
    (∀ (𝒢 : GroupModel (AbVar.zero K) L) (𝒢' : GroupModel (AbVar.zero K) L'),
      𝒢'.height = 𝒢.height) ∧
    (∀ 𝒰 𝒢 : GroupModel (AbVar.zero K) L, 𝒰.height = 𝒢.height) ∧
    (∀ 𝒢₁ 𝒢₂ 𝒢₃ : GroupModel (AbVar.zero K) L, 𝒢₁.height + 𝒢₂.height ≤ 𝒢₃.height) := by
  refine ⟨fun 𝒢 𝒢' => ?_, fun 𝒰 𝒢 => ?_, fun 𝒢₁ 𝒢₂ 𝒢₃ => ?_⟩ <;>
    simp only [groupModel_height_zero, add_zero, le_refl]

end ZeroInstances

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

/-! ### leaf-adopt3 fold: bridges to `LeafAdopt.H5` and to g0-split's `HeightAdditivity`

No theorem of h5-neron concludes `LeafAdopt.H5` or either of its halves for a general `A`:
`NeronModelMinimal` is a *hypothesis* of every reduction, and `StableHeightFinite` is proved only for
the zero abelian variety (`stableHeightFinite_zero`). The bridges below therefore take `LeafAdopt.H5`
(the bundle field `ResearchLeaves.h5`) as the source of `NeronModelMinimal`. -/

namespace ZInQ.H5Neron

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

/-- **H5, the form R19-R21 need, from the bundle field `h5`** (its `NeronModelMinimal` half), N1, N2
and the three base-change glue statements. -/
theorem stableFaltingsHeight_eq_neron_all_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hbc : ModelHeightBaseChange)
    (hbcE : GroupModelBaseChangeExists) (hop : OpenSubgroupHeight)
    (K : Type) [Field K] [NumberField K] (A : ZInQ.DefFaltings.AbVar K) :
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra K L₀)
      (𝒩₀ : ZInQ.DefFaltings.GroupModel A L₀),
      𝒩₀.IsNeronModel ∧ ZInQ.DefFaltings.stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L₀ L']
        [IsScalarTower K L₀ L'] (𝒩' : ZInQ.DefFaltings.GroupModel A L'), 𝒩'.IsNeronModel →
        ZInQ.DefFaltings.stableFaltingsHeight A = 𝒩'.height :=
  stableFaltingsHeight_eq_neron_all hN1 hN2 h5.2 hbc hbcE hop K A

/-- **Additivity `h(A) + h(B) ≤ h(C)` for `C ≅ A × B`, from the bundle field `h5`**, N1 and P2. -/
theorem stableFaltingsHeight_add_le_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists)
    (hH : ProductModelHeight) {K : Type} [Field K] (A B C : ZInQ.DefFaltings.AbVar K)
    (hC : IsProductAbVar C A B) :
    ZInQ.DefFaltings.stableFaltingsHeight A + ZInQ.DefFaltings.stableFaltingsHeight B ≤
      ZInQ.DefFaltings.stableFaltingsHeight C :=
  stableFaltingsHeight_add_le' hN1 h5.2 hH A B C hC

/-- **g0-split's glue piece `HeightAdditivity`, with `IsProductOf` unfolded** (g0-split's
`HSyn.G0Split.HeightAdditivity` and `IsProductOf` come later in this file, so they cannot be named
here). From N1, `NeronModelMinimal` and P2 (`ProductModelHeight`). The bridge, to be placed after
g0-split's definitions:
`fun L _ _ P A Z ⟨p₁, p₂, h₁, h₂, h⟩ => heightAdditivity_unfolded hN1 hmin hH L P A Z p₁ p₂ h₁ h₂ h`. -/
theorem heightAdditivity_unfolded (hN1 : NeronModelExists)
    (hmin : ZInQ.DefFaltings.NeronModelMinimal) (hH : ProductModelHeight) :
    ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L)
      (p₁ : P.X ⟶ A.X) (p₂ : P.X ⟶ Z.X), IsMonHom p₁ → IsMonHom p₂ → IsIso (CartesianMonoidalCategory.lift p₁ p₂) →
      ∀ a z p : ℝ, ZInQ.DefFaltings.stableFaltingsHeight A = a →
        ZInQ.DefFaltings.stableFaltingsHeight Z = z →
        ZInQ.DefFaltings.stableFaltingsHeight P = p → a + z ≤ p := by
  intro L _ _ P A Z p₁ p₂ h₁ h₂ hiso a z p ha hz hp
  have hC : IsProductAbVar P A Z := by
    refine ⟨asIso (CartesianMonoidalCategory.lift p₁ p₂), ?_, ?_⟩
    · rw [asIso_hom, CartesianMonoidalCategory.lift_fst]; exact h₁
    · rw [asIso_hom, CartesianMonoidalCategory.lift_snd]; exact h₂
  have key := stableFaltingsHeight_add_le' hN1 hmin hH A Z P hC
  rw [ha, hz, hp] at key
  exact_mod_cast key

end ZInQ.H5Neron

end H5NeronSec
