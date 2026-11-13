import Mathlib
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.B3Unram.B3b
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T
import ZInQKernel.HDecomp.Textbook.SkolemNoether
import ZInQKernel.Contrib.TwistDescent.GaloisDescent

/-! # Part 1. scratch/morph-descend/Descend.lean lines 3-401 (verbatim) -/
section PartDescend

/-!
# morph-descend: the input `MorphismsDescend` of G4 (EGA IV₃ 8.8.2), proved

Report: `docs/research/morph-descend.md`. Headline: `MorphDescend.morphismsDescend`, the Prop
`MorphismsDescend` of `scratch/g4-weilres/G4.lean` (copied verbatim below), proved with no
hypotheses, no `sorry`, only the standard axioms.

The geometric input is Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(`Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`, tagged Stacks 01ZC): for a cofiltered
diagram `Dᵢ` of qcqs schemes with affine transition maps and limit `lim Dᵢ`, every `S`-morphism
`lim Dᵢ → Y` with `Y` locally of finite presentation over `S` factors through some `Dᵢ`.
The glue proved here:
* `ringCoconeIsColimit`: `ℚ̄` is the filtered colimit in `CommRingCat` of its finite subextensions
  containing a number field `E₀`;
* `specConeIsLimit`: hence `Spec ℚ̄ = lim Spec L` in `Over (Spec K)` (`Spec` is a right adjoint,
  `Over.forget` reflects connected limits);
* `bcConeIsLimit`: hence `X ×_K ℚ̄ = lim X ×_K L` (`Over.pullback` is a right adjoint,
  `Over.forget` preserves connected limits), with affine transition maps (`bcDiag_isAffineHom`) and
  qcqs terms when `X → Spec K` is qcqs;
* `exists_descend`: the general descent statement, for `X` qcqs and `Y` LFP over any field `K`;
* `morphismsDescend`: the instance for `PkgI3.AbVar` (proper ⇒ qcqs, smooth ⇒ LFP).
-/

open CategoryTheory Limits AlgebraicGeometry

namespace MorphDescend

abbrev Qbar : Type := AlgebraicClosure ℚ

variable (E₀ : IntermediateField ℚ Qbar)

/-- The finite subextensions of `ℚ̄` containing `E₀`, ordered by inclusion. -/
abbrev Idx : Type := {L : IntermediateField ℚ Qbar // FiniteDimensional ℚ L ∧ E₀ ≤ L}

instance : IsDirectedOrder (Idx E₀) where
  directed L₁ L₂ := by
    obtain ⟨L₁, h₁, e₁⟩ := L₁
    obtain ⟨L₂, h₂, e₂⟩ := L₂
    exact ⟨⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, e₁.trans le_sup_left⟩,
      show L₁ ≤ L₁ ⊔ L₂ from le_sup_left, show L₂ ≤ L₁ ⊔ L₂ from le_sup_right⟩

instance [FiniteDimensional ℚ E₀] : Nonempty (Idx E₀) := ⟨⟨E₀, inferInstance, le_rfl⟩⟩

/-- The diagram `L ↦ L` of rings. -/
noncomputable def ringDiag : Idx E₀ ⥤ CommRingCat where
  obj L := CommRingCat.of L.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `ℚ̄` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag E₀) where
  pt := CommRingCat.of Qbar
  ι := { app L := CommRingCat.ofHom (algebraMap L.1 Qbar)
         naturality _ _ _ := rfl }

/-- `ℚ̄ = colim L` over the finite subextensions containing `E₀`. -/
noncomputable def ringCoconeIsColimit [FiniteDimensional ℚ E₀] : IsColimit (ringCocone E₀) := by
  haveI : ReflectsColimit (ringDiag E₀) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : Qbar)
    have hx : _root_.IsIntegral ℚ x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    refine ⟨⟨E₀ ⊔ IntermediateField.adjoin ℚ {x},
      IntermediateField.finiteDimensional_sup _ _, le_sup_left⟩, ⟨x, ?_⟩, rfl⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ {x} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ _)
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩


/-! ### The base changes `X ×_K L` as a cofiltered limit -/

section Schemes

variable {K : Type} [Field K]

/-- `e : K → ℚ̄` with image in `L`, as a map `K → L`. -/
noncomputable def restrL (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀) (L : Idx E₀) : K →+* L.1 :=
  e.codRestrict L.1 (fun x => L.2.2 (he x))

/-- The inclusion `L ⊆ L'` in `CommRingCat`. -/
noncomputable abbrev inclL {L L' : Idx E₀} (h : L ≤ L') : CommRingCat.of L.1 ⟶ CommRingCat.of L'.1 :=
  CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom

/-- The inclusion `L ⊆ ℚ̄` in `CommRingCat`. -/
noncomputable abbrev toQbar (L : Idx E₀) : CommRingCat.of L.1 ⟶ CommRingCat.of Qbar :=
  CommRingCat.ofHom (algebraMap L.1 Qbar)

variable (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)

theorem restrL_inclL {L L' : Idx E₀} (h : L ≤ L') :
    CommRingCat.ofHom (restrL E₀ e he L) ≫ inclL E₀ h = CommRingCat.ofHom (restrL E₀ e he L') :=
  rfl

theorem restrL_toQbar (L : Idx E₀) :
    CommRingCat.ofHom (restrL E₀ e he L) ≫ toQbar E₀ L = CommRingCat.ofHom e :=
  rfl

theorem inclL_toQbar {L L' : Idx E₀} (h : L ≤ L') : inclL E₀ h ≫ toQbar E₀ L' = toQbar E₀ L :=
  rfl

/-- The diagram `L ↦ (Spec L → Spec K)` in `Over (Spec K)`. -/
noncomputable def specDiag : (Idx E₀)ᵒᵖ ⥤ Over (Spec (CommRingCat.of K)) where
  obj L := Over.mk (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop)))
  map f := Over.homMk (Spec.map (inclL E₀ (leOfHom f.unop))) (by
    dsimp
    rw [← Spec.map_comp, restrL_inclL])
  map_id L := by
    ext1
    show Spec.map (inclL E₀ _) = 𝟙 _
    rw [show inclL E₀ (leOfHom (𝟙 L).unop) = 𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    ext1
    show Spec.map (inclL E₀ _) = Spec.map (inclL E₀ _) ≫ Spec.map (inclL E₀ _)
    rw [← Spec.map_comp]
    rfl

/-- `Spec ℚ̄ → Spec K` as a cone over `specDiag`. -/
noncomputable def specCone : Cone (specDiag E₀ e he) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom e))
  π := { app L := Over.homMk (Spec.map (toQbar E₀ L.unop)) (by
          dsimp [specDiag]
          rw [← Spec.map_comp, restrL_toQbar])
         naturality L L' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          ext1
          show Spec.map (toQbar E₀ _) = Spec.map (toQbar E₀ _) ≫ Spec.map (inclL E₀ _)
          rw [← Spec.map_comp, inclL_toQbar] }

/-- `Spec ℚ̄ = lim Spec L` in `Over (Spec K)`. -/
noncomputable def specConeIsLimit [FiniteDimensional ℚ E₀] : IsLimit (specCone E₀ e he) := by
  haveI : IsConnected (Idx E₀)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit E₀).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro L L' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro L
    simp only [Iso.refl_hom, Category.id_comp]

variable (X : Over (Spec (CommRingCat.of K)))

/-- The diagram `L ↦ L ×_K X` of schemes, as a composite of functors. -/
noncomputable def bcDiag' : (Idx E₀)ᵒᵖ ⥤ Scheme :=
  (specDiag E₀ e he ⋙ Over.pullback X.hom) ⋙ Over.forget X.left

/-- `ℚ̄ ×_K X` as a cone over `bcDiag'`. -/
noncomputable def bcCone' : Cone (bcDiag' E₀ e he X) :=
  (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone (specCone E₀ e he))

/-- `ℚ̄ ×_K X = lim (L ×_K X)`, composite form. -/
noncomputable def bcCone'IsLimit [FiniteDimensional ℚ E₀] : IsLimit (bcCone' E₀ e he X) := by
  haveI : IsConnected (Idx E₀)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) (specConeIsLimit E₀ e he))

/-- The diagram `L ↦ L ×_K X` of schemes, written with explicit pullbacks. -/
noncomputable abbrev bcDiag : (Idx E₀)ᵒᵖ ⥤ Scheme where
  obj L := pullback (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom
  map {L L'} f := pullback.lift
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom ≫
        Spec.map (inclL E₀ (leOfHom f.unop)))
      (pullback.snd _ _) (by
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL, pullback.condition])
  map_id L := (bcDiag' E₀ e he X).map_id L
  map_comp f g := (bcDiag' E₀ e he X).map_comp f g

/-- `ℚ̄ ×_K X` as a cone over `bcDiag`, written with explicit pullbacks. -/
noncomputable abbrev bcCone : Cone (bcDiag E₀ e he X) where
  pt := pullback (Spec.map (CommRingCat.ofHom e)) X.hom
  π := { app L := pullback.lift
          (pullback.fst (Spec.map (CommRingCat.ofHom e)) X.hom ≫ Spec.map (toQbar E₀ L.unop))
          (pullback.snd _ _) (by
            rw [Category.assoc, ← Spec.map_comp, restrL_toQbar, pullback.condition])
         naturality L L' f := (bcCone' E₀ e he X).π.naturality f }

/-- `ℚ̄ ×_K X = lim (L ×_K X)`. -/
noncomputable def bcConeIsLimit [FiniteDimensional ℚ E₀] : IsLimit (bcCone E₀ e he X) :=
  bcCone'IsLimit E₀ e he X

theorem bcDiag_obj (L : (Idx E₀)ᵒᵖ) :
    (bcDiag E₀ e he X).obj L =
      pullback (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom := rfl

theorem bcDiag_map_fst {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    (bcDiag E₀ e he X).map f ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom ≫
        Spec.map (inclL E₀ (leOfHom f.unop)) :=
  pullback.lift_fst _ _ _

theorem bcDiag_map_snd {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    (bcDiag E₀ e he X).map f ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom :=
  pullback.lift_snd _ _ _

theorem bcCone_π_app_fst (L : (Idx E₀)ᵒᵖ) :
    (bcCone E₀ e he X).π.app L ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom e)) X.hom ≫ Spec.map (toQbar E₀ L.unop) :=
  pullback.lift_fst _ _ _

theorem bcCone_π_app_snd (L : (Idx E₀)ᵒᵖ) :
    (bcCone E₀ e he X).π.app L ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom e)) X.hom :=
  pullback.lift_snd _ _ _

end Schemes

/-! ### Descent of morphisms (EGA IV₃ 8.8.2 via Mathlib's Stacks 01ZC) -/

section Main

variable {K : Type} [Field K]

/-- The comparison `ℚ̄ ×_K X → L ×_K X` (written `X ×_{K,e} ℚ̄ → X ×_{K,e|L} L`). -/
noncomputable def cmp (X : Over (Spec (CommRingCat.of K))) (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (L : Idx E₀) :
    pullback X.hom (Spec.map (CommRingCat.ofHom e)) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e he L))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (toQbar E₀ L)) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, restrL_toQbar])

theorem bcDiag_compactSpace (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) [QuasiCompact X.hom] (L : (Idx E₀)ᵒᵖ) :
    CompactSpace ((bcDiag E₀ e he X).obj L) := by
  rw [bcDiag_obj]
  infer_instance

theorem bcDiag_quasiSeparatedSpace (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) [QuasiSeparated X.hom] (L : (Idx E₀)ᵒᵖ) :
    QuasiSeparatedSpace ((bcDiag E₀ e he X).obj L) := by
  rw [bcDiag_obj]
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

theorem bcDiag_isAffineHom (e : K →+* Qbar) (he : ∀ x, e x ∈ E₀)
    (X : Over (Spec (CommRingCat.of K))) {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    IsAffineHom ((bcDiag E₀ e he X).map f) := by
  have t := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) X.hom).flip
  have s : IsPullback (pullback.snd (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom)
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom) X.hom
      (Spec.map (inclL E₀ (leOfHom f.unop)) ≫
        Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop))) := by
    rw [← Spec.map_comp, restrL_inclL]
    exact (IsPullback.of_hasPullback _ _).flip
  have hP := IsPullback.of_right (h₁₁ := (bcDiag E₀ e he X).map f) (by
    rw [bcDiag_map_snd]; exact s) (bcDiag_map_fst E₀ e he X f) t
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance

/-- **Descent of morphisms from `ℚ̄` to a number field (EGA IV₃ 8.8.2 (i), surjectivity, for
`ℚ̄ = colim L`), proved from Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC).** Let `X, Y` be `K`-schemes, `X` quasi-compact quasi-separated over `K`, `Y` locally
of finite presentation over `K`, and `e₁, e₂ : K → ℚ̄` with images in the number field `E₀`. Every
`ℚ̄`-morphism `φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` is the base change of a morphism
`ψ : X ×_{K,e₁} L → Y ×_{K,e₂} L` for some number field `E₀ ⊆ L ⊆ ℚ̄`. -/
theorem exists_descend [FiniteDimensional ℚ E₀] (X Y : Over (Spec (CommRingCat.of K)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (e₁ e₂ : K →+* Qbar) (he₁ : ∀ x, e₁ x ∈ E₀) (he₂ : ∀ x, e₂ x ∈ E₀)
    (φ : pullback X.hom (Spec.map (CommRingCat.ofHom e₁)) ⟶
      pullback Y.hom (Spec.map (CommRingCat.ofHom e₂)))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ (L : Idx E₀) (ψ : pullback X.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e₁ he₁ L))) ⟶
        pullback Y.hom (Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L)))),
      φ ≫ cmp E₀ Y e₂ he₂ L = cmp E₀ X e₁ he₁ L ≫ ψ := by
  classical
  let D := bcDiag E₀ e₁ he₁ X
  let c := bcCone E₀ e₁ he₁ X
  have hc : IsLimit c := bcConeIsLimit E₀ e₁ he₁ X
  have h1 : ∀ i, CompactSpace (D.obj i) := bcDiag_compactSpace E₀ e₁ he₁ X
  have h2 : ∀ i, QuasiSeparatedSpace (D.obj i) := bcDiag_quasiSeparatedSpace E₀ e₁ he₁ X
  have h3 : ∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f) := bcDiag_isAffineHom E₀ e₁ he₁ X
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app L := pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e₁ he₁ L.unop))) X.hom ≫
        Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L.unop))
      naturality L L' f := by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L'.unop)))
          (bcDiag_map_fst E₀ e₁ he₁ X f)).trans ?_
        dsimp only
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL]
        exact (Category.comp_id _).symm }
  let a : c.pt ⟶ Y.left :=
    (pullbackSymmetry _ _).hom ≫ φ ≫ pullback.fst _ _
  have ha : c.π ≫ t = (Functor.const _).map (a ≫ Y.hom) := by
    ext L
    simp only [NatTrans.comp_app, Functor.const_map_app, t, a, c]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e₂ he₂ L.unop)))
      (bcCone_π_app_fst E₀ e₁ he₁ X L)).trans ?_
    dsimp only
    rw [Category.assoc, ← Spec.map_comp, restrL_toQbar, Category.assoc, Category.assoc,
      pullback.condition, reassoc_of% hφ, pullbackSymmetry_hom_comp_snd_assoc]
  obtain ⟨L, g, hg1, hg2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t Y.hom c hc a ha
  refine ⟨L.unop, (pullbackSymmetry _ _).hom ≫ pullback.lift g (pullback.fst _ _) hg2, ?_⟩
  have key : cmp E₀ X e₁ he₁ L.unop ≫ (pullbackSymmetry _ _).hom =
      (pullbackSymmetry _ _).inv ≫ c.π.app L := by
    apply pullback.hom_ext
    · simp only [c, Category.assoc]
      simp [cmp]
    · simp only [c, Category.assoc]
      simp [cmp]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_fst, reassoc_of% key, hg1]
    simp [cmp, a]
  · rw [Category.assoc, Category.assoc, Category.assoc, pullback.lift_snd, reassoc_of% key]
    simp only [c]
    simp [cmp, reassoc_of% hφ]

end Main

/-! ### `MorphismsDescend` of `scratch/g4-weilres/G4.lean`, for the project's abelian varieties

The definitions `specEmb`, `specIncl`, `cmpL` and the statement `MorphismsDescend` are copied
verbatim from `scratch/g4-weilres/G4.lean` (namespace `G4WeilRes`; there `Qbar` is
`GlueB3Unram.Qbar`, the same reducible abbreviation `AlgebraicClosure ℚ`). -/

section G4

open PkgI3

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `Spec ℚ̄ → Spec L` for a subfield `L ⊆ ℚ̄`. -/
noncomputable abbrev specIncl (L : IntermediateField ℚ Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Qbar))

/-- `Spec e = Spec(ℚ̄ ← L) ≫ Spec e'` when `e = (L ↪ ℚ̄) ∘ e'`. -/
theorem specEmb_factor (L : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L)
    (he : ∀ x, (e' x : Qbar) = e x) :
    specEmb K e = specIncl L ≫ Spec.map (CommRingCat.ofHom (e' : K →+* L)) := by
  rw [specEmb, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (he x).symm

/-- The comparison `A ×_{K,e} ℚ̄ → A ×_{K,e'} L` (the base-change square along `Spec ℚ̄ → Spec L`). -/
noncomputable def cmpL (L : IntermediateField ℚ Qbar) (X : CategoryTheory.Over (Spec (CommRingCat.of K)))
    (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x) :
    Limits.pullback X.hom (specEmb K e) ⟶
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (e' : K →+* L))) :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ specIncl L)
    (by rw [Limits.pullback.condition, specEmb_factor K L e e' he, Category.assoc])

/-- **Input of G4 (EGA IV₃ 8.8.2 (i), surjectivity part, for `ℚ̄ = colim L`).** Verbatim from
`scratch/g4-weilres/G4.lean`. -/
def MorphismsDescend : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (e₁' e₂' : K →ₐ[ℚ] L)
      (he₁ : ∀ x, (e₁' x : Qbar) = e₁ x) (he₂ : ∀ x, (e₂' x : Qbar) = e₂ x)
      (ψ : Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom (e₁' : K →+* L))) ⟶
        Limits.pullback B.X.hom (Spec.map (CommRingCat.ofHom (e₂' : K →+* L)))),
      φ.left ≫ cmpL K L B.X e₂ e₂' he₂ = cmpL K L A.X e₁ e₁' he₁ ≫ ψ

/-- The restriction `K → L` of `e : K → ℚ̄`, as a `ℚ`-algebra map. -/
noncomputable def restrAlg {E₀ : IntermediateField ℚ Qbar} (e : K →ₐ[ℚ] Qbar)
    (he : ∀ x, (e : K →+* Qbar) x ∈ E₀) (L : Idx E₀) : K →ₐ[ℚ] L.1 :=
  { restrL E₀ (e : K →+* Qbar) he L with
    commutes' := fun r => Subtype.ext (e.commutes r) }

/-- **`MorphismsDescend` holds (proved; no hypotheses).** Abelian varieties are proper (so
quasi-compact and quasi-separated) and smooth (so locally of finite presentation); apply
`exists_descend` with `E₀ = e₁(K) ⊔ e₂(K)`. -/
theorem morphismsDescend : MorphismsDescend := by
  intro K _ A B e₁ e₂ φ
  let E₀ : IntermediateField ℚ Qbar := e₁.fieldRange ⊔ e₂.fieldRange
  have : FiniteDimensional ℚ e₁.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e₁).toLinearEquiv
  have : FiniteDimensional ℚ e₂.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e₂).toLinearEquiv
  have : FiniteDimensional ℚ E₀ := IntermediateField.finiteDimensional_sup _ _
  have he₁ : ∀ x, (e₁ : K →+* Qbar) x ∈ E₀ := fun x =>
    (le_sup_left : e₁.fieldRange ≤ E₀) ⟨x, rfl⟩
  have he₂ : ∀ x, (e₂ : K →+* Qbar) x ∈ E₀ := fun x =>
    (le_sup_right : e₂.fieldRange ≤ E₀) ⟨x, rfl⟩
  obtain ⟨L, ψ, hψ⟩ := exists_descend E₀ A.X B.X (e₁ : K →+* Qbar) (e₂ : K →+* Qbar) he₁ he₂
    φ.left (CategoryTheory.Over.w φ)
  exact ⟨L.1, L.2.1, restrAlg K e₁ he₁ L, restrAlg K e₂ he₂ L, fun _ => rfl, fun _ => rfl, ψ, hψ⟩

end G4

end MorphDescend
end PartDescend

/-! # Part 2. scratch/inertia-homs/InertiaHoms.lean lines 7-2089 (verbatim; G4.lean + inertia-homs) -/
section PartInertia

/-!
# inertia-homs: the input `InertiaFixesHoms` of g4-weilres, corrected and proved from leaves

Report: `docs/research/inertia-homs.md`. This file is `scratch/g4-weilres/G4.lean` verbatim
(everything up to `end G4WeilRes` of that file), followed by the new part (from
`section NewConj` on). Headlines:

* `G4WeilRes.inertiaFixesHomsMon_of_leaves : NeronOggShafarevich → HomFreeFinite →
  InertiaFixesHomsMon` (NOS = Serre–Tate 1968 Thm 1, leaf `PkgI2.NeronOggShafarevich`;
  Mumford §19 Thm 3, leaf `PkgI3.HomFreeFinite`).
* `G4WeilRes.conjAction_inertia'`: the inertia hypothesis of G4 from `InertiaFixesHomsMon`.
* `G4WeilRes.homField_of_model_leaves'`: G4 from `HomFreeFinite`, `MorphismsDescend` and
  `NeronOggShafarevich` (the input `InertiaFixesHoms` is eliminated).

`InertiaFixesHomsMon` differs from g4-weilres's `InertiaFixesHoms` in two ways: it quantifies
over homomorphisms `φ : AbVar.Hom (bcAlong A e₁) (bcAlong B e₂)` only (the original quantifies over
all morphisms of schemes and is false for constant maps to points not fixed by inertia), and over
places `w` over a prime `p` (`LiesOver w p`), which is how its only consumer uses it.

No `sorry`, no `axiom`.
-/

/-!
# g4-weilres: glue step G4 of `docs/research/h-decomposition.md` (Weil restriction, Hom field)

Report: `docs/research/g4-weilres.md`. Headline: `G4WeilRes.homField_of_model_leaves`.

Contents, in order:
* `G4Conj` (generic, any category with pullbacks): the comparison `cmp` between base changes
  along `f₂ = s ≫ f₁` respects multiplication and unit; the conjugate `conj` of a morphism; the
  conjugate of a monoid homomorphism is one (`conj_isMonHom`); multiplicativity, functoriality.
* The bridge `GalUnramifiedOutside L T ↔ ∀ p ∉ T, UnramifiedAt L p` for finite Galois `L ⊆ ℚ̄`
  (`galUnramifiedOutside_iff`; the new direction via Mathlib's profinite transitivity and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`, as in glue-b3b's `exists_inertia_neg`).
* The Hom-field core (`homField_core`: Minkowski + infinite Galois theory) and its numerical form
  (`homField_le_heightD`).
* The Hom lattice of a finite family of abelian varieties over `ℚ̄`, its rank (leaf
  `PkgI3.HomFreeFinite`), its `ℓ`-adic faithfulness.
* The conjugates of a model `A/K` (`conjData`) and the conjugation action of `G_ℚ` on their Hom
  lattice (`conjAction`, `conjActionExists`): the Weil-restriction step, constructed.
* Continuity from EGA IV₃ 8.8.2 (`MorphismsDescend` → `conjAction_continuous`), inertia from good
  reduction (`InertiaFixesHoms` → `conjAction_inertia`), the headline, and the consumers
  (`b3_of_homField` for G7, `cm_degree_of_homField` for the CM branch).

Inputs are `def … : Prop` hypotheses; no `sorry`, no `axiom`.
-/

section ConjSec

/-!
## Part A: conjugating homomorphisms of base-changed group objects

Generic category theory (any `C` with pullbacks). For a monoid object `X` over `S` and two base
changes along `f₁, f₂ : T → S` with `f₂ = s ≫ f₁`, the comparison `g : X ×_{S,f₂} T → X ×_{S,f₁} T`
(over `s : T → T`) respects the multiplications, and the conjugate of a monoid homomorphism along
`g` (the unique lift through the pullback square) is a monoid homomorphism.
In the application `S = Spec K`, `T = Spec ℚ̄`, `f₁ = Spec e`, `s = Spec σ`, `f₂ = Spec (σ ∘ e)`.
-/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- The multiplication of the base change, followed by the projection to `X`. -/
theorem mul_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (μ[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f =
      pullback.lift (pullback.fst _ _ ≫ pullback.fst X.hom f)
        (pullback.snd _ _ ≫ pullback.fst X.hom f)
        (by
          simp only [Category.assoc, pullback.condition]
          exact pullback.condition_assoc f) ≫ μ[X].left := by
  show ((Functor.LaxMonoidal.μ (Over.pullback f) X X) ≫ (Over.pullback f).map μ[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    exact Over.μ_pullback_left_fst_fst X X
  · simp only [Category.assoc, pullback.lift_snd]
    exact Over.μ_pullback_left_fst_snd X X


/-- The unit of the base change, followed by the projection to `X`. -/
theorem one_left_fst (f : T ⟶ S) (X : Over S) [MonObj X] :
    (η[(Over.pullback f).obj X]).left ≫ pullback.fst X.hom f = f ≫ η[X].left := by
  show ((Functor.LaxMonoidal.ε (Over.pullback f)) ≫ (Over.pullback f).map η[X]).left ≫ _ = _
  rw [Over.comp_left, Category.assoc]
  erw [pullback.lift_fst]
  rw [← Category.assoc, Over.ε_pullback_left]
  congr 1
  rw [IsIso.inv_comp_eq]
  have := pullback.condition (f := 𝟙 S) (g := f)
  simpa using this

/-! ### The comparison map over `s` -/

section Cmp

variable (X : Over S) {f₁ f₂ : T ⟶ S} (s : T ⟶ T) (h : f₂ = s ≫ f₁)

/-- `X ×_{f₂} T → X ×_{f₁} T` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def cmp : pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

@[reassoc (attr := simp)]
theorem cmp_fst : cmp X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp_snd : cmp X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s :=
  pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem cmp_isPullback :
    IsPullback (cmp X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : cmp X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [cmp_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [cmp_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

/-- `cmp` on the self-products. -/
noncomputable def cmp2 :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ cmp X s h) (pullback.snd _ _ ≫ cmp X s h) (by
    show (pullback.fst _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ cmp X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, cmp_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem cmp2_fst : cmp2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cmp X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cmp2_snd : cmp2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ cmp X s h :=
  pullback.lift_snd _ _ _

/-- **The comparison respects the multiplications.** -/
theorem cmp_mul [MonObj X] :
    (μ[(Over.pullback f₂).obj X]).left ≫ cmp X s h =
      cmp2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, mul_left_fst, mul_left_fst,
      ← Category.assoc (cmp2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, cmp2_fst_assoc, cmp_fst]
    · simp only [Category.assoc, pullback.lift_snd, cmp2_snd_assoc, cmp_fst]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      cmp2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [cmp2_fst_assoc, cmp_snd, Category.assoc]

/-- **The comparison respects the units.** -/
theorem cmp_one [MonObj X] :
    (η[(Over.pullback f₂).obj X]).left ≫ cmp X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, one_left_fst, Category.assoc, one_left_fst, h, Category.assoc]
  · rw [Category.assoc, cmp_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end Cmp


/-! ### Conjugating morphisms -/

section ConjMor

variable (X Y : Over S) {f₁ f₂ g₁ g₂ : T ⟶ S} (s : T ⟶ T) (hf : f₂ = s ≫ f₁) (hg : g₂ = s ≫ g₁)

/-- Two maps into `Y ×_{g₂} T` agreeing after `cmp` and after the structure map are equal. -/
theorem ext_cmp {Z : C} (a b : Z ⟶ pullback Y.hom g₂) (h1 : a ≫ cmp Y s hg = b ≫ cmp Y s hg)
    (h2 : a ≫ pullback.snd Y.hom g₂ = b ≫ pullback.snd Y.hom g₂) : a = b := by
  apply pullback.hom_ext _ h2
  rw [← cmp_fst Y s hg, ← Category.assoc, h1, Category.assoc]

/-- **The conjugate of a morphism** `φ : X_{f₁} → Y_{g₁}` (over `T`): the morphism
`X_{f₂} → Y_{g₂}` with `σφ ∘ cmp = cmp ∘ φ` (`conj_cmp`), unique (`conj_unique`). -/
noncomputable def conj (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y :=
  Over.homMk (pullback.lift (cmp X s hf ≫ φ.left ≫ pullback.fst Y.hom g₁)
    (pullback.snd X.hom f₂) (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
      rw [reassoc_of% hw, cmp_snd_assoc, hg]))
    (pullback.lift_snd _ _ _)

@[reassoc]
theorem conj_cmp (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ).left ≫ cmp Y s hg = cmp X s hf ≫ φ.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, cmp_fst]
    exact pullback.lift_fst _ _ _
  · simp only [Category.assoc, cmp_snd]
    have hw : φ.left ≫ pullback.snd Y.hom g₁ = pullback.snd X.hom f₁ := Over.w φ
    rw [hw, cmp_snd]
    exact pullback.lift_snd_assoc _ _ _ _

theorem conj_unique (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y)
    (ψ : (Over.pullback f₂).obj X ⟶ (Over.pullback g₂).obj Y)
    (hψ : ψ.left ≫ cmp Y s hg = cmp X s hf ≫ φ.left) : ψ = conj X Y s hf hg φ := by
  apply Over.OverMorphism.ext
  apply ext_cmp Y s hg
  · rw [hψ, conj_cmp]
  · exact (Over.w ψ).trans (Over.w (conj X Y s hf hg φ)).symm

theorem tensor_cmp2 (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (conj X Y s hf hg φ ⊗ₘ conj X Y s hf hg φ).left ≫ cmp2 Y s hg =
      cmp2 X s hf ≫ (φ ⊗ₘ φ).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, Category.assoc]
    erw [Over.tensorHom_left_fst_assoc, Over.tensorHom_left_fst]
    rw [conj_cmp, cmp2_fst_assoc]
  · rw [Category.assoc, cmp2_snd, Category.assoc]
    erw [Over.tensorHom_left_snd_assoc, Over.tensorHom_left_snd]
    rw [conj_cmp, cmp2_snd_assoc]

/-- **The conjugate of a monoid homomorphism is a monoid homomorphism.** -/
theorem conj_isMonHom [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) [IsMonHom φ] :
    IsMonHom (conj X Y s hf hg φ) where
  one_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_one, Category.assoc,
        ← Over.comp_left, IsMonHom.one_hom, cmp_one]
    · exact (Over.w _).trans (Over.w _).symm
  mul_hom := by
    apply Over.OverMorphism.ext
    apply ext_cmp Y s hg
    · rw [Over.comp_left, Category.assoc, conj_cmp, ← Category.assoc, cmp_mul, Category.assoc,
        ← Over.comp_left, IsMonHom.mul_hom, Over.comp_left, Over.comp_left, Category.assoc,
        cmp_mul, reassoc_of% (tensor_cmp2 X Y s hf hg φ)]
    · exact (Over.w _).trans (Over.w _).symm

/-- `conj_isMonHom` with the hypothesis explicit (for instances found only up to unfolding). -/
theorem conj_isMonHom' [MonObj X] [MonObj Y]
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) (hφ : IsMonHom φ) :
    IsMonHom (conj X Y s hf hg φ) :=
  conj_isMonHom X Y s hf hg φ

theorem lift_cmp2 (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    (lift (conj X Y s hf hg φ) (conj X Y s hf hg ψ)).left ≫ cmp2 Y s hg =
      cmp X s hf ≫ (lift φ ψ).left := by
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · rw [Category.assoc, cmp2_fst, pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst,
      conj_cmp]
  · rw [Category.assoc, cmp2_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
      conj_cmp]

/-- **Conjugation is multiplicative** for the pointwise product of morphisms into a monoid. -/
theorem conj_mul [MonObj Y] (φ ψ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg (φ * ψ) = conj X Y s hf hg φ * conj X Y s hf hg ψ := by
  symm
  apply conj_unique
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_mul,
    ← Category.assoc, lift_cmp2, Category.assoc]

theorem conj_one [MonObj Y] :
    conj X Y s hf hg (1 : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) = 1 := by
  symm
  apply conj_unique
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc, cmp_one,
    ← Category.assoc, ← Category.assoc]
  congr 1
  have e1 : (toUnit ((Over.pullback f₂).obj X)).left = pullback.snd X.hom f₂ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₂).obj X)))
  have e2 : (toUnit ((Over.pullback f₁).obj X)).left = pullback.snd X.hom f₁ :=
    (Category.comp_id _).symm.trans (Over.w (toUnit ((Over.pullback f₁).obj X)))
  rw [e1, e2]
  exact (cmp_snd X s hf).symm

/-- Conjugation along equal maps `s = s'` agrees. -/
theorem conj_congr {s' : T ⟶ T} (hs : s = s') (hf' : f₂ = s' ≫ f₁) (hg' : g₂ = s' ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf hg φ = conj X Y s' hf' hg' φ := by
  subst hs; rfl

/-- `cmp` along the identity is the identity. -/
theorem cmp_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) : cmp X s hf₀ = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [cmp_snd, hs, Category.comp_id, Category.id_comp]

/-- Conjugation along the identity is the identity. -/
theorem conj_self (hs : s = 𝟙 T) (hf₀ : f₁ = s ≫ f₁) (hg₀ : g₁ = s ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y s hf₀ hg₀ φ = φ := by
  symm
  apply conj_unique
  rw [cmp_self X s hs hf₀, cmp_self Y s hs hg₀]
  erw [Category.comp_id, Category.id_comp]

/-- `cmp` composes. -/
theorem cmp_comp {f₃ : T ⟶ S} (s' : T ⟶ T) (h₃₂ : f₃ = s' ≫ f₂) (h₃₁ : f₃ = (s' ≫ s) ≫ f₁) :
    cmp X (s' ≫ s) h₃₁ = cmp X s' h₃₂ ≫ cmp X s hf := by
  apply pullback.hom_ext
  · simp
  · simp

/-- **Conjugation composes.** -/
theorem conj_comp {f₃ g₃ : T ⟶ S} (s' : T ⟶ T) (hf₃₂ : f₃ = s' ≫ f₂) (hg₃₂ : g₃ = s' ≫ g₂)
    (hf₃₁ : f₃ = (s' ≫ s) ≫ f₁) (hg₃₁ : g₃ = (s' ≫ s) ≫ g₁)
    (φ : (Over.pullback f₁).obj X ⟶ (Over.pullback g₁).obj Y) :
    conj X Y (s' ≫ s) hf₃₁ hg₃₁ φ = conj X Y s' hf₃₂ hg₃₂ (conj X Y s hf hg φ) := by
  symm
  apply conj_unique
  rw [cmp_comp Y s hg s' hg₃₂ hg₃₁, cmp_comp X s hf s' hf₃₂ hf₃₁, conj_cmp_assoc, conj_cmp,
    Category.assoc]

end ConjMor

end G4Conj

end ConjSec

namespace G4WeilRes

open GlueB3Unram GlueDescent.B2Q NumberField
open scoped Pointwise

/-! ## Places over `p` exist -/

/-- There is a valuation subring of `ℚ̄` over every prime `p`. -/
theorem exists_liesOver (p : ℕ) (hp : p.Prime) : ∃ w : ValuationSubring Qbar, LiesOver w p := by
  let A : Subring Qbar := ⊥
  let pA : A := ⟨(p : Qbar), by simpa using (⊥ : Subring Qbar).natCast_mem p⟩
  let I : Ideal A := Ideal.span {pA}
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := by rw [h]; trivial
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp a.2
    have h2 : ((n * p : ℤ) : Qbar) = ((1 : ℤ) : Qbar) := by
      have := congrArg Subtype.val ha
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      push_cast
      rw [hn]; exact this
    have h3 : n * (p : ℤ) = 1 := Int.cast_injective h2
    have h4 : (p : ℤ) ∣ 1 := ⟨n, by rw [← h3]; ring⟩
    have := Int.eq_one_of_dvd_one (by positivity) h4
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  refine ⟨B, ?_⟩
  have hmem : (p : Qbar) ∈ B.nonunits := hB ⟨pA, Ideal.subset_span rfl, rfl⟩
  exact (ValuationSubring.mem_nonunits_iff B).mp hmem

/-! ## A Galois automorphism maps a normal subfield into itself -/

theorem map_mem_of_normal (L : IntermediateField ℚ Qbar) [Normal ℚ L] (σ : Gal) {y : Qbar}
    (hy : y ∈ L) : σ y ∈ L := by
  have h := AlgEquiv.restrictNormal_commutes σ L ⟨y, hy⟩
  rw [← show algebraMap L Qbar ⟨y, hy⟩ = y from rfl, ← h]
  exact (AlgEquiv.restrictNormal σ L ⟨y, hy⟩).2

/-! ## Lifting a residually trivial automorphism of `L` into an inertia group -/

/-- `σ` acts trivially modulo `w` on the algebraic integers of `L`. -/
def ResTrivOn (L : IntermediateField ℚ Qbar) (w : ValuationSubring Qbar) (σ : Gal) : Prop :=
  ∀ y : Qbar, IsIntegral ℤ y → y ∈ L → w.valuation (σ y - y) < 1

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **The inertia lift.** Let `L ⊆ ℚ̄` be finite Galois, `w` a place over `p` and `σ ∈ G_ℚ`
acting trivially modulo `w` on the algebraic integers of `L`. Then some `s ∈ I_w` agrees with
`σ` on `L`. -/
theorem exists_inertia_restrict (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime) (w : ValuationSubring Qbar) (hw : LiesOver w p)
    (σ : Gal) (hσ : ResTrivOn L w σ) :
    ∃ s : Gal, s ∈ inertiaGQ w ∧ ∀ y ∈ L, s y = σ y := by
  classical
  let H : Subgroup Gal := L.fixingSubgroup
  have hH : ∀ g : Gal, g ∈ H ↔ ∀ y ∈ L, g y = y := fun g =>
    IntermediateField.mem_fixingSubgroup_iff L g
  have hHopen : IsOpen (H : Set Gal) := IntermediateField.fixingSubgroup_isOpen L
  have hHclosed : IsClosed (H : Set Gal) := Subgroup.isClosed_of_isOpen H hHopen
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hHclosed.isCompact
  let A := FixedPoints.subalgebra ℤ B H
  let Q := centerIdeal w
  haveI : SMulCommClass H A B := ⟨fun h a b => by
    rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_eq_mul, smul_eq_mul, smul_mul', a.2 h]⟩
  -- elements of `A` lie in `L`
  have hAL : ∀ a : A, ((a : B) : Qbar) ∈ L := by
    intro a
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    intro g hg
    have := a.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hAint : ∀ a : A, IsIntegral ℤ ((a : B) : Qbar) := fun a =>
    (mem_integralClosure_iff ℤ Qbar).mp (a : B).2
  -- the valuation input on `A`
  have hAval : ∀ (a : A) (τ : Gal), ResTrivOn L w τ →
      w.valuation (((a : B) : Qbar) - τ ((a : B) : Qbar)) < 1 := by
    intro a τ hτ
    rw [Valuation.map_sub_swap]
    exact hτ _ (hAint a) (hAL a)
  -- `σ⁻¹` is also residually trivial on `L`
  have hσi : ResTrivOn L w σ⁻¹ := by
    intro y hy hyL
    have hy' : IsIntegral ℤ ((σ⁻¹ : Gal) y) := hy.map ((σ⁻¹ : Gal) : Qbar →+* Qbar).toIntAlgHom
    have h := hσ _ hy' (map_mem_of_normal L σ⁻¹ hyL)
    have hss : σ ((σ⁻¹ : Gal) y) = y := by
      show (σ * σ⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [hss, Valuation.map_sub_swap] at h
    exact h
  -- step 1: `σ • Q` and `Q` lie over the same prime of `A`
  have hunder : (σ • Q).under A = Q.under A := by
    ext a
    rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal]
    have h := hAval a σ⁻¹ hσi
    show w.valuation ((σ⁻¹ : Gal) ((a : B) : Qbar)) < 1 ↔ w.valuation ((a : B) : Qbar) < 1
    constructor
    · intro h1
      have : ((a : B) : Qbar) = (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) +
          (σ⁻¹ : Gal) ((a : B) : Qbar) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h h1)
    · intro h1
      have : (σ⁻¹ : Gal) ((a : B) : Qbar) = ((a : B) : Qbar) -
          (((a : B) : Qbar) - (σ⁻¹ : Gal) ((a : B) : Qbar)) := by ring
      rw [this]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1 h)
  -- step 2: transitivity over `A` gives `τ` stabilizing `Q` and agreeing with `σ` on `L`
  haveI hσQ : (σ • Q).IsPrime := by
    show (σ • centerIdeal w).IsPrime
    rw [← centerIdeal_smul]; infer_instance
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := A) (G := H)
    (σ • Q) Q hunder
  let τ : Gal := (g : Gal) * σ
  have hτQ : τ • Q = Q := by
    show ((g : Gal) * σ) • Q = Q
    rw [mul_smul]; exact hg.symm
  have hτL : ∀ y ∈ L, τ y = σ y := by
    intro y hy
    show (g : Gal) (σ y) = σ y
    exact (hH g).mp g.2 _ (map_mem_of_normal L σ hy)
  have hτ : ResTrivOn L w τ := by
    intro y hy hyL
    rw [hτL y hyL]; exact hσ y hy hyL
  -- step 3: `τ` induces an `A/P`-automorphism of `B/Q`
  let f : B ≃+* B := MulSemiringAction.toRingEquiv Gal B τ
  have hQf : Q = Q.map f := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨τ⁻¹ • b, ?_, by simp [f]⟩
      rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hτQ]; exact hb
    · rintro ⟨x, hx, rfl⟩
      rw [← hτQ]
      exact Ideal.smul_mem_pointwise_smul_iff.mpr hx
  let e : (B ⧸ Q) ≃+* (B ⧸ Q) := Ideal.quotientEquiv Q Q f hQf
  have he : ∀ b : B, e (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (τ • b) := fun b => rfl
  let φ : (B ⧸ Q) ≃ₐ[A ⧸ Q.under A] (B ⧸ Q) := AlgEquiv.ofRingEquiv (f := e) (by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, he, Ideal.Quotient.eq, mem_centerIdeal]
    have h := hAval a τ hτ
    rw [Valuation.map_sub_swap] at h
    exact h)
  -- step 4: Mathlib's surjectivity gives `h' ∈ H` acting on `B/Q` as `τ`
  obtain ⟨h', hh'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under A) Q φ
  have hact : ∀ b : B, Ideal.Quotient.mk Q (((h' : H) : Gal) • b) =
      Ideal.Quotient.mk Q (τ • b) := by
    intro b
    have := congrArg (fun ψ => ψ (Ideal.Quotient.mk Q b)) hh'
    exact this
  let k : Gal := ((h' : H) : Gal)
  have hkQ : k • Q = Q := h'.2
  have hkL : ∀ y ∈ L, k y = y := (hH k).mp (h' : H).2
  let s : Gal := k⁻¹ * τ
  refine ⟨s, ?_, ?_⟩
  · apply mem_inertia_of_center hp hw s
    · show (k⁻¹ * τ) • Q = Q
      rw [mul_smul, hτQ, inv_smul_eq_iff, hkQ]
    · intro b
      have h1 := hact (s • b)
      have h2 : ((h' : H) : Gal) • (s • b) = τ • b := by
        show k • ((k⁻¹ * τ) • b) = τ • b
        rw [mul_smul, smul_inv_smul]
      rw [h2, Ideal.Quotient.eq] at h1
      have h3 : b - s • b ∈ Q := by
        have h4 : τ • (b - s • b) ∈ τ • Q := by rw [hτQ, smul_sub]; exact h1
        rwa [Ideal.smul_mem_pointwise_smul_iff] at h4
      have := Q.neg_mem h3
      rwa [neg_sub] at this
  · intro y hy
    show k⁻¹ (τ y) = σ y
    rw [hτL y hy]
    have hk' : k⁻¹ ∈ H := H.inv_mem (h' : H).2
    exact (hH _).mp hk' _ (map_mem_of_normal L σ hy)

/-! ## The bridge -/

/-- `P.under ℤ = (p)` for a prime of `𝓞 L` containing the prime `p`. -/
theorem under_eq_span {L : IntermediateField ℚ Qbar} [NumberField L] (p : ℕ) (hp : p.Prime)
    (P : Ideal (𝓞 L)) [P.IsPrime] (hpP : ((p : ℤ) : 𝓞 L) ∈ P) :
    P.under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := by
    rw [Ideal.under, Ideal.mem_comap]; simpa using hpP
  have hle : Ideal.span {(p : ℤ)} ≤ P.under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ (𝓞 L)) P).ne_top hle).symm

/-- **Bridge (glue, proved).** If every inertia group of `G_ℚ` over `p` fixes the finite Galois
field `L ⊆ ℚ̄`, then `L` is unramified at `p` in glue-descent's ideal-theoretic sense. -/
theorem unramifiedAt_of_inertia_le (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    [IsGalois ℚ L] (p : ℕ) (hp : p.Prime)
    (h : ∀ w : ValuationSubring Qbar, LiesOver w p → inertiaGQ w ≤ L.fixingSubgroup) :
    UnramifiedAt L p := by
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  intro P hP hpP
  obtain ⟨w, hw⟩ := exists_liesOver p hp
  let P₀ : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal w).comap (embW L w)
  haveI hP₀prime : P₀.IsPrime := Ideal.comap_isPrime _ _
  have hpP₀ : ((p : ℤ) : 𝓞 L) ∈ P₀ := by
    show embW L w ((p : ℤ) : 𝓞 L) ∈ IsLocalRing.maximalIdeal w
    rw [ValuationSubring.valuation_lt_one_iff]
    have : ((embW L w ((p : ℤ) : 𝓞 L) : w) : Qbar) = (p : Qbar) := by
      simp [embW, emb]
    rw [this]; exact hw
  let G := L ≃ₐ[ℚ] L
  have hunder : P.under ℤ = P₀.under ℤ := by
    rw [under_eq_span p hp P hpP, under_eq_span p hp P₀ hpP₀]
  -- the inertia group of `P₀` in `Gal(L/ℚ)` is trivial
  have htriv : ∀ g ∈ P₀.inertia G, g = 1 := by
    intro g hg
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (E := Qbar) (K₁ := L) g
    have hσL : ∀ x : L, algebraMap L Qbar (g x) = σ (algebraMap L Qbar x) := by
      intro x
      rw [← hσ]; exact AlgEquiv.restrictNormal_commutes σ L x
    have hres : ResTrivOn L w σ := by
      intro y hy hyL
      let x : 𝓞 L := ⟨⟨y, hyL⟩, by
        rw [mem_integralClosure_iff]
        exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Qbar)
          (algebraMap L Qbar).injective).mp hy⟩
      have hx := (Ideal.mem_inertia.mp hg) x
      change embW L w (g • x - x) ∈ IsLocalRing.maximalIdeal w at hx
      rw [ValuationSubring.valuation_lt_one_iff] at hx
      have he1 : ((embW L w (g • x - x) : w) : Qbar) = emb L (g • x) - emb L x := by
        show emb L (g • x - x) = _
        rw [map_sub]
      have he2 : emb L (g • x) = σ y := by
        simp only [emb, RingHom.comp_apply]
        rw [show σ y = σ (algebraMap L Qbar ⟨y, hyL⟩) from rfl, ← hσL]
        rfl
      have he : ((embW L w (g • x - x) : w) : Qbar) = σ y - y := by
        rw [he1, he2]; rfl
      rw [he] at hx; exact hx
    obtain ⟨s, hs, hsL⟩ := exists_inertia_restrict L p hp w hw σ hres
    have hsfix := (IntermediateField.mem_fixingSubgroup_iff L s).mp (h w hw hs)
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L Qbar).injective
    rw [hσL x]
    show σ (x : Qbar) = (x : Qbar)
    rw [← hsL _ x.2, hsfix _ x.2]
  have hcard : Nat.card (P₀.inertia G) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ((htriv a a.2).trans (htriv b b.2).symm)⟩, ⟨1⟩⟩
  have e₀ : P₀.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G,
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := G) (P₀.under ℤ) P₀, hcard]
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under ℤ) P G, hunder,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P₀.under ℤ) P₀ G, e₀]

/-- The Galois form of "unramified outside `T`" gives glue-descent's form at every `p ∉ T`. -/
theorem unramifiedAt_of_galUnramifiedOutside (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) (h : GalUnramifiedOutside L T) :
    ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  fun p hpT => unramifiedAt_of_inertia_le L p p.2 (fun w hw => h p p.2 hpT w hw)

/-- And conversely (glue-b3-unram's bridge): the two forms agree on finite Galois fields. -/
theorem galUnramifiedOutside_iff (L : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ L] [IsGalois ℚ L] (T : Finset ℕ) :
    GalUnramifiedOutside L T ↔ ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p :=
  ⟨unramifiedAt_of_galUnramifiedOutside L T, fun h p hp hpT w hw =>
    inertia_le_of_unramifiedAt L p hp (h ⟨p, hp⟩ hpT) w hw⟩


/-! ## The Hom field: the core theorem (Minkowski + infinite Galois theory + the bridge)

N5 L544-563, with the Weil restriction `W₀ = Res_{K/ℚ} A` replaced by what the argument uses of
it: a free `ℤ`-module `M` of rank `r` (the geometric endomorphism lattice of `W₀`, i.e. the direct
sum of the Hom groups among the conjugates of `A`) with a `ℤ`-linear action of `G_ℚ` that is
continuous (every element has an open stabilizer: each geometric homomorphism is defined over a
number field) and on which every inertia group over a prime `p ∉ T` acts trivially. -/

section Core

variable {M : Type*} [AddCommGroup M]

/-- The `GL_r(ℤ)`-realization of the automorphisms of a free `ℤ`-module with a basis. -/
noncomputable def toGL {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    (M ≃ₗ[ℤ] M) →* Matrix.GeneralLinearGroup (Fin r) ℤ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ M).symm.toMonoidHom

theorem toGL_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ M) :
    Function.Injective (toGL b) := by
  intro f g h
  have h1 := congrArg (fun u : Matrix.GeneralLinearGroup (Fin r) ℤ =>
    (u : Matrix (Fin r) (Fin r) ℤ)) h
  have h2 : (f : M →ₗ[ℤ] M) = g := (LinearMap.toMatrixAlgEquiv b).injective h1
  exact LinearEquiv.toLinearMap_injective h2

theorem toGL_eq_one_iff {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (f : M ≃ₗ[ℤ] M) :
    toGL b f = 1 ↔ f = 1 :=
  ⟨fun h => toGL_injective b (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- An automorphism is the identity iff it fixes a basis. -/
theorem eq_one_iff_basis {ι : Type*} (b : Module.Basis ι ℤ M) (f : M ≃ₗ[ℤ] M) :
    f = 1 ↔ ∀ i, f (b i) = b i := by
  constructor
  · intro h i; rw [h]; rfl
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    simpa using h i

/-- **G4, the Hom field (core, proved).** Let `K ⊆ ℚ̄` be finite Galois, unramified outside `T`
(Galois form), and let `G_ℚ` act `ℤ`-linearly on a free `ℤ`-module `M` with basis indexed by
`Fin r`, continuously (open stabilizers), with every inertia group over every prime `p ∉ T`
acting trivially. Then there is a finite Galois `L ⊇ K` such that `G_L` acts trivially on `M`
(`L` defines every element of `M`), `[L:ℚ] ≤ [K:ℚ]·3^{r²}` (Minkowski), and `L` is unramified
outside `T`, in both the Galois form and glue-descent's ideal-theoretic form. -/
theorem homField_core (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ Module.finrank ℚ K * 3 ^ (r ^ 2) ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact toGL_eq_one_iff b (ρ σ)
  -- the kernel is open
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  haveI hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  haveI hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  -- `[E:ℚ] = |ρ(G_ℚ)| ≤ 3^{r²}`
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  have hE3 : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := by
    rw [hcardE]; exact GlueRepo.TorsionFree.card_le_three_pow ρ'.range
  -- `L = E ⊔ K`
  refine ⟨E ⊔ K, inferInstance, inferInstance, le_sup_right, ?_, ?_, ?_, ?_⟩
  · intro σ hσ
    have h1 : σ ∈ E.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hσ
    rw [hE] at h1
    exact h1
  · calc Module.finrank ℚ ↥(E ⊔ K) ≤ Module.finrank ℚ E * Module.finrank ℚ K :=
          IntermediateField.finrank_sup_le E K
      _ ≤ 3 ^ (r ^ 2) * Module.finrank ℚ K := Nat.mul_le_mul_right _ hE3
      _ = Module.finrank ℚ K * 3 ^ (r ^ 2) := Nat.mul_comm _ _
  · have hgal : GalUnramifiedOutside (E ⊔ K) T := by
      intro p hp hpT w hw s hs
      rw [IntermediateField.fixingSubgroup_sup]
      refine ⟨?_, hK p hp hpT w hw hs⟩
      rw [hE]
      exact hinert p hp hpT w hw s hs
    exact hgal
  · apply unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨?_, hK p hp hpT w hw hs⟩
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 with the manuscript's numbers.** If `[K:ℚ] ≤ F₀ = 324!` and `r ≤ 16F₀²` (N5 L547-548),
the Hom field has `[L:ℚ] ≤ D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`). -/
theorem homField_le_heightD (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨L, h1, h2, hKL, hdef, hdeg, hgal, hram⟩ := homField_core K b ρ hcont T hK hinert
  refine ⟨L, h1, h2, hKL, hdef, ?_, hgal, hram⟩
  exact hdeg.trans (GlueRepo.Numerics.a8_degree ZInQ.Compiler.Precision.heightD_eq hKF le_rfl hr)

end Core


/-! ## The lattice of the conjugates: rank, faithfulness, and the abelian-variety instantiation

The manuscript's `End(W₀_ℚ̄) = ⊕_{σ,τ} Hom(σA, τA)`: here the direct sum over ordered pairs of
`n` abelian varieties over `ℚ̄` (the conjugates of `A`, `n ≤ [K:ℚ] ≤ F₀`), as a product of
`PkgI3.AbVar.Hom` groups. -/

section Lattice

/-- **Rank of the lattice (glue, proved).** A product over ordered pairs `(i, j) ∈ n × n` of free
finite `ℤ`-modules of rank `≤ c` is free and finite of rank `≤ c·n²`. -/
theorem pi_rank_le {ι : Type*} [Fintype ι] {c : ℕ} (H : ι × ι → Type*) [∀ ij, AddCommGroup (H ij)]
    [∀ ij, Module.Free ℤ (H ij)] [∀ ij, Module.Finite ℤ (H ij)]
    (hH : ∀ ij, Module.finrank ℤ (H ij) ≤ c) :
    Module.finrank ℤ (∀ ij, H ij) ≤ c * Fintype.card ι ^ 2 := by
  rw [Module.finrank_pi_fintype]
  calc ∑ ij, Module.finrank ℤ (H ij) ≤ ∑ _ij : ι × ι, c :=
        Finset.sum_le_sum fun ij _ => hH ij
    _ = c * Fintype.card ι ^ 2 := by simp [Fintype.card_prod, sq, mul_comm]

/-- **Inertia acts trivially on the lattice (glue, proved; N5 L559-561).** If the lattice `M`
embeds equivariantly and injectively into a module `N` (in the application: `ℓ`-adic
realization, `Hom(σA, τA) → Hom_{ℤ_ℓ}(T_ℓ σA, T_ℓ τA)`, injective by Mumford §19 Thm 3, the leaf
`PkgI3.HomFreeFinite`), then every `s` acting trivially on `N` (in the application: inertia at
`p ∉ T`, by Néron–Ogg–Shafarevich, the leaf `PkgI2.NeronOggShafarevich`) acts trivially on `M`. -/
theorem trivial_of_faithful {G M N : Type*} [Group G] [AddCommGroup M] [AddCommGroup N]
    (ρ : G →* (M ≃ₗ[ℤ] M)) (τ : G →* (N ≃ₗ[ℤ] N)) (ι : M →+ N) (hι : Function.Injective ι)
    (heq : ∀ g m, ι (ρ g m) = τ g (ι m)) (s : G) (hs : τ s = 1) : ρ s = 1 := by
  apply LinearEquiv.ext
  intro m
  apply hι
  rw [heq, hs]
  rfl

/-- The `ℓ`-adic side: if `s` acts trivially on the Tate modules `T i`, it acts trivially on
`Hom_{ℤ_ℓ}(T i, T j)` by conjugation. -/
theorem conj_trivial {R : Type*} [CommRing R] {T₁ T₂ : Type*} [AddCommGroup T₁] [Module R T₁]
    [AddCommGroup T₂] [Module R T₂] (a₁ : T₁ ≃ₗ[R] T₁) (a₂ : T₂ ≃ₗ[R] T₂) (h₁ : a₁ = 1)
    (h₂ : a₂ = 1) (φ : T₁ →ₗ[R] T₂) :
    (a₂ : T₂ →ₗ[R] T₂) ∘ₗ φ ∘ₗ (a₁.symm : T₁ →ₗ[R] T₁) = φ := by
  subst h₁; subst h₂; rfl

open PkgI3 PkgI3.AbVar CategoryTheory MonObj

/-- The geometric Hom lattice of `n` abelian varieties over `ℚ̄`: `⊕_{(i,j)} Hom(A i, A j)`. -/
abbrev HomLattice {Idx : Type} (A : Idx → AbVar Qbar) : Type :=
  ∀ ij : Idx × Idx, AbVar.Hom (A ij.1) (A ij.2)

/-- **Mumford's bound on the lattice (from the leaf `HomFreeFinite`).** For abelian surfaces
`A i` over `ℚ̄`, the lattice `⊕ Hom(A i, A j)` is free and finite of rank `≤ 16n²`. -/
theorem homLattice_free (hHFF : HomFreeFinite) {Idx : Type} [Fintype Idx] (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2) :
    Module.Free ℤ (HomLattice A) ∧ Module.Finite ℤ (HomLattice A) ∧
      Module.finrank ℤ (HomLattice A) ≤ 16 * Fintype.card Idx ^ 2 := by
  haveI : ∀ ij : Idx × Idx, Module.Free ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).1
  haveI : ∀ ij : Idx × Idx, Module.Finite ℤ (AbVar.Hom (A ij.1) (A ij.2)) :=
    fun ij => (hHFF Qbar (A ij.1) (A ij.2)).2.1
  refine ⟨inferInstance, inferInstance, pi_rank_le _ fun ij => ?_⟩
  have h := (hHFF Qbar (A ij.1) (A ij.2)).2.2.1
  rw [hdim, hdim] at h
  have h16 : ((Module.finrank ℤ (AbVar.Hom (A ij.1) (A ij.2)) : ℕ∞) : WithBot ℕ∞) ≤
      (((16 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    refine h.trans (le_of_eq ?_)
    rfl
  exact_mod_cast h16

/-- **The `ℓ`-adic realization is faithful (from the leaf `HomFreeFinite`).** `Hom(A, B) →
Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective for `ℓ` invertible in `k`: `HomFreeFinite` gives
injectivity on `ℤ_ℓ ⊗ Hom(A, B)`, and `Hom(A, B) → ℤ_ℓ ⊗ Hom(A, B)` is injective because
`Hom(A, B)` is free (flat) and `ℤ → ℤ_ℓ` is injective. This is the `ι` of `trivial_of_faithful`
in the application (N5 L559-561). -/
theorem tateHom_injective (hHFF : HomFreeFinite) {k : Type} [Field k] (A B : AbVar k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) : Function.Injective (tateHom ℓ A B) := by
  have hinj := (hHFF k A B).2.2.2 ℓ hℓ
  haveI : Module.Free ℤ (AbVar.Hom A B) := (hHFF k A B).1
  let j : AbVar.Hom A B →ₗ[ℤ] TensorProduct ℤ ℤ_[ℓ] (AbVar.Hom A B) :=
    ((Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.toLinearMap
  have hj : Function.Injective j := by
    have h1 : Function.Injective (Algebra.linearMap ℤ ℤ_[ℓ]) := by
      intro a b hab
      exact Int.cast_injective hab
    exact (Module.Flat.rTensor_preserves_injective_linearMap _ h1).comp
      (TensorProduct.lid ℤ (AbVar.Hom A B)).symm.injective
  have hcomp : ∀ f, tateHomZl ℓ A B (j f) = tateHom ℓ A B f := by
    intro f
    have hjf : j f = (1 : ℤ_[ℓ]) ⊗ₜ[ℤ] f := by
      show (Algebra.linearMap ℤ ℤ_[ℓ]).rTensor (AbVar.Hom A B)
        ((TensorProduct.lid ℤ (AbVar.Hom A B)).symm f) = _
      erw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul]
      congr 1
    rw [hjf]
    exact (TensorProduct.lift.tmul _ _).trans (one_smul _ _)
  intro f g hfg
  apply hj
  apply hinj
  rw [hcomp, hcomp]
  exact hfg


/-- The `ℓ`-adic realization of the lattice: `f ↦ (T_ℓ(f_{ij}))_{ij}`. -/
noncomputable def tateLattice (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type} (A : Idx → AbVar Qbar) :
    HomLattice A →+ (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) :=
  Pi.addMonoidHom fun ij => (tateHom ℓ (A ij.1) (A ij.2)).comp (Pi.evalAddMonoidHom _ ij)

/-- The realization of the lattice is injective (leaf `HomFreeFinite`; `ℓ ≠ 0` in `ℚ̄`). -/
theorem tateLattice_injective (hHFF : HomFreeFinite) (ℓ : ℕ) [hℓ : Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) : Function.Injective (tateLattice ℓ A) := by
  intro f g h
  funext ij
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.out.ne_zero
  exact tateHom_injective hHFF (A ij.1) (A ij.2) ℓ hne (congrFun h ij)

/-- **The inertia hypothesis from the `ℓ`-adic side (glue, proved).** If `G_ℚ` acts on the
realization `∏ Hom_{ℤ_ℓ}(T_ℓ A_i, T_ℓ A_j)` compatibly with `ρ` (equivariance: open, needs the
action on points), and inertia over `p ∉ T` acts trivially there (Néron–Ogg–Shafarevich for the
conjugates, which have good reduction above `p ∉ T`, G3), then `hinert` of
`homField_of_conjugates` holds. -/
theorem inertia_of_tate (hHFF : HomFreeFinite) (ℓ : ℕ) [Fact ℓ.Prime] {Idx : Type}
    (A : Idx → AbVar Qbar) (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (τ : Gal →* ((∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ) ≃ₗ[ℤ]
      (∀ ij : Idx × Idx, (A ij.1).T ℓ →ₗ[ℤ_[ℓ]] (A ij.2).T ℓ)))
    (heq : ∀ σ m, tateLattice ℓ A (ρ σ m) = τ σ (tateLattice ℓ A m)) (T : Finset ℕ)
    (htate : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, τ s = 1) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1 :=
  fun p hp hpT w hw s hs => trivial_of_faithful ρ τ (tateLattice ℓ A)
    (tateLattice_injective hHFF ℓ A) heq s (htate p hp hpT w hw s hs)


/-- **G4 on the abelian-variety layer.** Let `K ⊆ ℚ̄` be finite Galois with `[K:ℚ] ≤ F₀`,
unramified outside `T`; let `A 0, …, A (n-1)` be abelian surfaces over `ℚ̄` (the conjugates of
the fibre object, indexed by a finite type of size `≤ F₀`, e.g. the embeddings `K → ℚ̄`), and let `G_ℚ` act `ℤ`-linearly on `⊕ Hom(A i, A j)` (the conjugation
action; its construction is the open part of G4) continuously and with every inertia group over
`p ∉ T` acting trivially. Then the Hom field `L ⊇ K` exists: finite Galois, `[L:ℚ] ≤ D`, every
element of the lattice is fixed by `G_L`, and `L` is unramified outside `T` (both forms).
Leaf used: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3). -/
theorem homField_of_conjugates (hHFF : HomFreeFinite)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {Idx : Type} [Fintype Idx] (hn : Fintype.card Idx ≤ ZInQ.heightF0) (A : Idx → AbVar Qbar)
    (hdim : ∀ i, (A i).dim = 2)
    (ρ : Gal →* (HomLattice A ≃ₗ[ℤ] HomLattice A))
    (hcont : ∀ m : HomLattice A, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) := by
  obtain ⟨hfree, hfin, hrank⟩ := homLattice_free hHFF A hdim
  have hr : Module.finrank ℤ (HomLattice A) ≤ 16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 2))
  exact homField_le_heightD K hKF hr (Module.finBasisOfFinrankEq ℤ (HomLattice A) rfl) ρ hcont T
    hK hinert

/-! ### The conjugation action

For `σ ∈ G_ℚ`, a conjugate of an abelian variety `X` over `ℚ̄` is an `X'` with a pullback square
`X' → X` over `Spec σ : Spec ℚ̄ → Spec ℚ̄` (the relation used by leaf-qm-fp's `IsBaseChangeOf`).
`ConjData` records a finite family closed under conjugation: `A i` is the `σ`-conjugate of
`A (σ⁻¹·i)` through `g σ i : A i → A (σ⁻¹·i)`. `IsConjAction D ρ` says that `ρ σ` sends
`f : A (σ⁻¹·i) → A (σ⁻¹·j)` to its conjugate `σf : A i → A j`, the morphism with
`g σ j ∘ σf = f ∘ g σ i`. Such a `ρ` is unique (`isConjAction_unique`), and for the conjugates of
a model `A/K` it exists (`conjAction`, `conjActionExists`). -/

open AlgebraicGeometry

/-- `Spec σ : Spec ℚ̄ → Spec ℚ̄`. -/
noncomputable abbrev specGal (σ : Gal) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom (σ : Qbar →+* Qbar))

theorem specGal_mul (σ τ : Gal) : specGal (σ * τ) = specGal σ ≫ specGal τ := by
  rw [specGal, specGal, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specGal_one : specGal 1 = 𝟙 _ := by
  rw [specGal, show CommRingCat.ofHom ((1 : Gal) : Qbar →+* Qbar) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

/-- Conjugation data for a finite family of abelian varieties over `ℚ̄`: a permutation action of
`G_ℚ` on the indices and, for every `σ` and `i`, a pullback square exhibiting `A i` as the base
change of `A (σ⁻¹·i)` along `Spec σ`. -/
structure ConjData (Idx : Type) where
  A : Idx → AbVar Qbar
  act : Gal → Equiv.Perm Idx
  g : ∀ (σ : Gal) (i : Idx), (A i).X.left ⟶ (A ((act σ).symm i)).X.left
  pb : ∀ (σ : Gal) (i : Idx),
    IsPullback (g σ i) (A i).X.hom (A ((act σ).symm i)).X.hom (specGal σ)

/-- `ρ` is the conjugation action for the data `D`. -/
def IsConjAction {Idx : Type} (D : ConjData Idx)
    (ρ : Gal → HomLattice D.A → HomLattice D.A) : Prop :=
  ∀ (σ : Gal) (f : HomLattice D.A) (i j : Idx),
    (ρ σ f (i, j)).hom.left ≫ D.g σ j =
      D.g σ i ≫ (f ((D.act σ).symm i, (D.act σ).symm j)).hom.left

/-- **The conjugation action is unique (glue, proved).** -/
theorem isConjAction_unique {Idx : Type} (D : ConjData Idx)
    {ρ ρ' : Gal → HomLattice D.A → HomLattice D.A}
    (h : IsConjAction D ρ) (h' : IsConjAction D ρ') : ρ = ρ' := by
  funext σ f
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  apply CategoryTheory.Over.OverMorphism.ext
  apply (D.pb σ j).hom_ext
  · rw [h σ f i j, h' σ f i j]
  · rw [CategoryTheory.Over.w, CategoryTheory.Over.w]

/-- The conjugation action exists (proved below for the conjugates of a model, `conjActionExists`). -/
def ConjActionExists {Idx : Type} (D : ConjData Idx) : Prop :=
  ∃ ρ : Gal →* (HomLattice D.A ≃ₗ[ℤ] HomLattice D.A), IsConjAction D (fun σ f => ρ σ f)

/-! ### The conjugates of a model over a number field

For `A/K` with `K ⊆ ℚ̄` a number field, the conjugates are the base changes `A_e = A ×_{K,e} ℚ̄`
along the embeddings `e : K → ℚ̄`; `G_ℚ` permutes the embeddings, and the comparison maps
`G4Conj.cmp` give the squares `A_e → A_{σ⁻¹∘e}` over `Spec σ`. -/

/-- Base change of an abelian variety along a ring homomorphism `f : K → L` of fields
(as `PkgI3.AbVar.baseChange`, for an arbitrary embedding). -/
noncomputable def bcAlong {K L : Type} [Field K] [Field L] (A : AbVar K) (f : K →+* L) :
    AbVar L :=
  let F := CategoryTheory.Over.pullback (Spec.map (CommRingCat.ofHom f))
  letI : GrpObj (F.obj A.X) := Functor.grpObjObj
  haveI : IsProper (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : Smooth (F.obj A.X).hom := by dsimp [F]; infer_instance
  haveI : GeometricallyIntegral (F.obj A.X).hom := by dsimp [F]; infer_instance
  { X := F.obj A.X }

variable (K : IntermediateField ℚ Qbar)

/-- `Spec e : Spec ℚ̄ → Spec K` for an embedding `e : K → ℚ̄`. -/
noncomputable abbrev specEmb (e : K →ₐ[ℚ] Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (e : K →+* Qbar))

/-- `G_ℚ` permutes the embeddings `K → ℚ̄`: `σ · e = σ ∘ e`. -/
noncomputable def embAct (σ : Gal) : Equiv.Perm (K →ₐ[ℚ] Qbar) where
  toFun e := (σ : Qbar →ₐ[ℚ] Qbar).comp e
  invFun e := ((σ⁻¹ : Gal) : Qbar →ₐ[ℚ] Qbar).comp e
  left_inv e := by
    ext x
    show (σ⁻¹ * σ) (e x) = e x
    rw [inv_mul_cancel]; rfl
  right_inv e := by
    ext x
    show (σ * σ⁻¹) (e x) = e x
    rw [mul_inv_cancel]; rfl

theorem specEmb_act (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K (embAct K σ e) = specGal σ ≫ specEmb K e := by
  rw [specEmb, specEmb, specGal, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem specEmb_symm (σ : Gal) (e : K →ₐ[ℚ] Qbar) :
    specEmb K e = specGal σ ≫ specEmb K ((embAct K σ).symm e) :=
  (congrArg (specEmb K) ((embAct K σ).apply_symm_apply e)).symm.trans (specEmb_act K σ _)

/-- **The conjugation data of a model `A/K`** (constructed, no hypothesis): the `[K:ℚ]`
conjugates `A_e`, permuted by `G_ℚ`, with their pullback squares over `Spec σ`. -/
noncomputable def conjData (A : AbVar K) : ConjData (K →ₐ[ℚ] Qbar) where
  A e := bcAlong A (e : K →+* Qbar)
  act σ := embAct K σ
  g σ e := G4Conj.cmp A.X (specGal σ) (specEmb_symm K σ e)
  pb σ e := G4Conj.cmp_isPullback A.X (specGal σ) (specEmb_symm K σ e)

/-- There are `[K:ℚ]` conjugates. -/
theorem card_conjugates [FiniteDimensional ℚ K] :
    Fintype.card (K →ₐ[ℚ] Qbar) = Module.finrank ℚ K :=
  AlgHom.card ℚ K Qbar

section Action

open CategoryTheory MonObj

variable (A : AbVar K)

/-- Conjugation of one Hom group: `Hom(A_{σ⁻¹i}, A_{σ⁻¹j}) → Hom(A_i, A_j)`, additive
(`G4Conj.conj_mul`, `conj_one`), landing in homomorphisms (`G4Conj.conj_isMonHom`). -/
noncomputable def conjHom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) :
    AbVar.Hom ((conjData K A).A ((embAct K σ).symm i)) ((conjData K A).A ((embAct K σ).symm j)) →+
      AbVar.Hom ((conjData K A).A i) ((conjData K A).A j) where
  toFun φ :=
    haveI hc : IsMonHom (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
        G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom) :=
      G4Conj.conj_isMonHom' A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j)
        φ.hom (show IsMonHom φ.hom from inferInstance)
    AbVar.Hom.mk' (show ((conjData K A).A i).X ⟶ ((conjData K A).A j).X from
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom)
  map_zero' := AbVar.Hom.ext'
    (G4Conj.conj_one A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j))
  map_add' φ ψ := AbVar.Hom.ext'
    (G4Conj.conj_mul A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom ψ.hom)

theorem conjHom_hom (σ : Gal) (i j : K →ₐ[ℚ] Qbar) (φ) :
    (conjHom K A σ i j φ).hom =
      G4Conj.conj A.X A.X (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) φ.hom := rfl

/-- The action of `σ` on the lattice `⊕ Hom(A_i, A_j)`. -/
noncomputable def conjAct (σ : Gal) :
    HomLattice (conjData K A).A →+ HomLattice (conjData K A).A :=
  AddMonoidHom.pi fun ij => (conjHom K A σ ij.1 ij.2).comp
    (Pi.evalAddMonoidHom (fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
      AbVar.Hom ((conjData K A).A ij.1) ((conjData K A).A ij.2))
      ((embAct K σ).symm ij.1, (embAct K σ).symm ij.2))

theorem conjAct_apply (σ : Gal) (m : HomLattice (conjData K A).A) (i j : K →ₐ[ℚ] Qbar) :
    conjAct K A σ m (i, j) = conjHom K A σ i j (m ((embAct K σ).symm i, (embAct K σ).symm j)) :=
  rfl

theorem conjAct_isConjAction : IsConjAction (conjData K A) (fun σ m => conjAct K A σ m) := by
  intro σ m i j
  dsimp only
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_cmp A.X A.X _ _ _ _

theorem conjAct_one (m : HomLattice (conjData K A).A) : conjAct K A 1 m = m := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  exact G4Conj.conj_self A.X A.X (specGal 1) specGal_one _ _ _

theorem conjAct_mul (σ τ : Gal) (m : HomLattice (conjData K A).A) :
    conjAct K A (σ * τ) m = conjAct K A σ (conjAct K A τ m) := by
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjAct_apply, conjHom_hom, conjHom_hom, conjAct_apply, conjHom_hom]
  have hi : specEmb K i = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm i)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  have hj : specEmb K j = (specGal σ ≫ specGal τ) ≫
      specEmb K ((embAct K τ).symm ((embAct K σ).symm j)) := by
    rw [Category.assoc, ← specEmb_symm, ← specEmb_symm]
  exact (G4Conj.conj_congr A.X A.X (specGal (σ * τ)) _ _ (specGal_mul σ τ) hi hj _).trans
    (G4Conj.conj_comp A.X A.X (specGal τ) (specEmb_symm K τ _) (specEmb_symm K τ _)
      (specGal σ) (specEmb_symm K σ i) (specEmb_symm K σ j) hi hj _)

/-- **The conjugation action of `G_ℚ` on the Hom lattice of the conjugates (constructed).** -/
noncomputable def conjAction : Gal →* (HomLattice (conjData K A).A ≃ₗ[ℤ]
    HomLattice (conjData K A).A) where
  toFun σ := LinearEquiv.ofLinearMap (conjAct K A σ).toIntLinearMap
    (conjAct K A σ⁻¹).toIntLinearMap
    (LinearMap.ext fun m => by
      show conjAct K A σ (conjAct K A σ⁻¹ m) = m
      rw [← conjAct_mul, mul_inv_cancel, conjAct_one])
    (LinearMap.ext fun m => by
      show conjAct K A σ⁻¹ (conjAct K A σ m) = m
      rw [← conjAct_mul, inv_mul_cancel, conjAct_one])
  map_one' := LinearEquiv.ext fun m => conjAct_one K A m
  map_mul' σ τ := LinearEquiv.ext fun m => conjAct_mul K A σ τ m

theorem conjAction_apply (σ : Gal) (m : HomLattice (conjData K A).A) :
    conjAction K A σ m = conjAct K A σ m := rfl

/-- **The Weil-restriction step of G4 is glue, proved: the conjugation action exists.** -/
theorem conjActionExists : ConjActionExists (conjData K A) :=
  ⟨conjAction K A, conjAct_isConjAction K A⟩

end Action

/-- **G4 for a model `A/K` (the manuscript's statement, N5 L544-563).** Let `K ⊆ ℚ̄` be finite
Galois with `[K:ℚ] ≤ F₀`, unramified outside `T` (G2), and `A/K` an abelian surface whose
conjugates `A_e` are surfaces. Let `ρ = conjAction K A` be the conjugation action of `G_ℚ` on
`⊕_{e,e'} Hom(A_e, A_{e'})` (constructed; the unique action with `IsConjAction`). If `ρ` is
continuous and inertia outside `T` acts trivially, the Hom field `L ⊇ K` exists: finite Galois,
`[L:ℚ] ≤ D`, every geometric homomorphism among the conjugates is fixed by `G_L`, `L`
unramified outside `T` (both forms). Leaf: `PkgI3.HomFreeFinite`. -/
theorem homField_of_model (hHFF : HomFreeFinite) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (hcont : ∀ m : HomLattice (conjData K A).A, IsOpen {σ : Gal | conjAction K A σ m = m})
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_conjugates hHFF K hKF (by rw [card_conjugates]; exact hKF) (conjData K A).A hdim
    (conjAction K A) hcont T hK hinert

/-! ### Continuity of the conjugation action from the descent of morphisms

`HomDescends` is the input: a homomorphism between conjugates is fixed by conjugation through an
open subgroup of `G_ℚ`. It is a consequence of EGA IV₃ 8.8.2 (a morphism between base changes to
`ℚ̄ = colim L` of finitely presented `K`-schemes is the base change of a morphism over some number
field `L`; locator UNVERIFIED) together with the descent bookkeeping "conjugation by `σ ∈ G_L`
fixes a morphism defined over `L`" (`conj_unique` on the pasted squares `ℚ̄ → L → K`), which is
glue not formalized here. Stated as a `Prop` over the genuine objects (`PkgI3.AbVar`, Mathlib's
pullbacks, `G4Conj.conj`). -/

/-- **Input (EGA IV₃ 8.8.2 + descent bookkeeping; not formalized).** For abelian varieties
`A, B` over a number field `K ⊆ ℚ̄` and embeddings `e₁, e₂ : K → ℚ̄`, every morphism
`A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` is fixed by the conjugation of an open subgroup of
`G_ℚ` (those `σ` fixing `e₁(K)`, `e₂(K)` and the field of definition). -/
def HomDescends : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ U : Subgroup Gal, IsOpen (U : Set Gal) ∧ ∀ σ ∈ U,
      ∀ (hf : specEmb K e₁ = specGal σ ≫ specEmb K e₁)
        (hg : specEmb K e₂ = specGal σ ≫ specEmb K e₂),
        G4Conj.conj A.X B.X (specGal σ) hf hg φ = φ

/-- `Spec ℚ̄ → Spec L` for a subfield `L ⊆ ℚ̄`. -/
noncomputable abbrev specIncl (L : IntermediateField ℚ Qbar) :
    Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom (algebraMap L Qbar))

/-- `Spec e = Spec(ℚ̄ ← L) ≫ Spec e'` when `e = (L ↪ ℚ̄) ∘ e'`. -/
theorem specEmb_factor (L : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L)
    (he : ∀ x, (e' x : Qbar) = e x) :
    specEmb K e = specIncl L ≫ Spec.map (CommRingCat.ofHom (e' : K →+* L)) := by
  rw [specEmb, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (he x).symm

/-- The comparison `A ×_{K,e} ℚ̄ → A ×_{K,e'} L` (the base-change square along `Spec ℚ̄ → Spec L`). -/
noncomputable def cmpL (L : IntermediateField ℚ Qbar) (X : CategoryTheory.Over (Spec (CommRingCat.of K)))
    (e : K →ₐ[ℚ] Qbar) (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x) :
    Limits.pullback X.hom (specEmb K e) ⟶
      Limits.pullback X.hom (Spec.map (CommRingCat.ofHom (e' : K →+* L))) :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ specIncl L)
    (by rw [Limits.pullback.condition, specEmb_factor K L e e' he, Category.assoc])

/-- **Input: EGA IV₃ 8.8.2 (i), surjectivity part, for `ℚ̄ = colim L` (locator UNVERIFIED).**
Every morphism `A ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` over `ℚ̄` between base changes of abelian
varieties over a number field `K ⊆ ℚ̄` comes from a morphism `ψ : A ×_{K,e₁'} L → B ×_{K,e₂'} L`
over a number field `L ⊆ ℚ̄` through which `e₁, e₂` factor (`φ` is the base change of `ψ`: it
is the map compatible with `ψ` under the cartesian squares `cmpL`). Hypotheses of 8.8.2: `A`
quasi-compact quasi-separated (proper), `B` locally of finite presentation (smooth). -/
def MorphismsDescend : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X),
    ∃ (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (e₁' e₂' : K →ₐ[ℚ] L)
      (he₁ : ∀ x, (e₁' x : Qbar) = e₁ x) (he₂ : ∀ x, (e₂' x : Qbar) = e₂ x)
      (ψ : Limits.pullback A.X.hom (Spec.map (CommRingCat.ofHom (e₁' : K →+* L))) ⟶
        Limits.pullback B.X.hom (Spec.map (CommRingCat.ofHom (e₂' : K →+* L)))),
      φ.left ≫ cmpL K L B.X e₂ e₂' he₂ = cmpL K L A.X e₁ e₁' he₁ ≫ ψ

/-- `σ ∈ G_L` fixes `Spec ℚ̄ → Spec L`. -/
theorem specGal_specIncl (L : IntermediateField ℚ Qbar) (σ : Gal) (hσ : σ ∈ L.fixingSubgroup) :
    specGal σ ≫ specIncl L = specIncl L := by
  rw [specGal, specIncl, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp hσ x x.2

/-- **`HomDescends` from EGA IV₃ 8.8.2 (glue, proved): the descent bookkeeping.** A morphism
that is the base change of one over `L` is fixed by conjugation through `G_L`. -/
theorem homDescends_of_morphismsDescend (hM : MorphismsDescend) : HomDescends := by
  intro K _ A B e₁ e₂ φ
  obtain ⟨L, hL, e₁', e₂', he₁, he₂, ψ, hψ⟩ := hM K A B e₁ e₂ φ
  refine ⟨L.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen L, fun σ hσ hf hg => ?_⟩
  symm
  apply G4Conj.conj_unique
  -- `cmp_σ ≫ cmpL = cmpL`
  have hcL : ∀ (X : CategoryTheory.Over (Spec (CommRingCat.of K))) (e : K →ₐ[ℚ] Qbar)
      (e' : K →ₐ[ℚ] L) (he : ∀ x, (e' x : Qbar) = e x)
      (h : specEmb K e = specGal σ ≫ specEmb K e),
      G4Conj.cmp X (specGal σ) h ≫ cmpL K L X e e' he = cmpL K L X e e' he := by
    intro X e e' he h
    apply Limits.pullback.hom_ext
    · simp [cmpL]
    · simp only [cmpL, Category.assoc, Limits.pullback.lift_snd]
      rw [G4Conj.cmp_snd_assoc, specGal_specIncl L σ hσ]
  apply Limits.pullback.hom_ext
  · have e1 : Limits.pullback.fst B.X.hom (specEmb K e₂) =
        cmpL K L B.X e₂ e₂' he₂ ≫ Limits.pullback.fst _ _ := by simp [cmpL]
    rw [Category.assoc, G4Conj.cmp_fst, Category.assoc, e1, reassoc_of% hψ,
      reassoc_of% (hcL A.X e₁ e₁' he₁ hf)]
  · rw [Category.assoc, G4Conj.cmp_snd, Category.assoc]
    have h1 : φ.left ≫ Limits.pullback.snd B.X.hom (specEmb K e₂) =
        Limits.pullback.snd A.X.hom (specEmb K e₁) := CategoryTheory.Over.w φ
    rw [reassoc_of% h1, h1, G4Conj.cmp_snd]

/-- `G_K` fixes every embedding of the Galois field `K`. -/
theorem embAct_symm_of_mem [IsGalois ℚ K] (σ : Gal) (hσ : σ ∈ K.fixingSubgroup)
    (e : K →ₐ[ℚ] Qbar) : (embAct K σ).symm e = e := by
  ext x
  have hx : e x ∈ K := by
    have hmem : e x ∈ e.fieldRange := ⟨x, rfl⟩
    rw [AlgHom.fieldRange_of_normal e] at hmem
    exact hmem
  have hσ' : σ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hσ
  exact (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ hx

/-- The stabilizer of a lattice element, as a subgroup. -/
def stabSub (A : AbVar K) (m : HomLattice (conjData K A).A) : Subgroup Gal where
  carrier := {σ | conjAction K A σ m = m}
  one_mem' := by simp
  mul_mem' {σ τ} hσ hτ := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, LinearEquiv.mul_apply, hτ, hσ]
  inv_mem' {σ} hσ := by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hσ]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

/-- **Continuity of the conjugation action (glue, proved from `HomDescends`).** -/
theorem conjAction_continuous (hD : HomDescends) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (m : HomLattice (conjData K A).A) :
    IsOpen {σ : Gal | conjAction K A σ m = m} := by
  classical
  choose U hUo hU using fun ij : (K →ₐ[ℚ] Qbar) × (K →ₐ[ℚ] Qbar) =>
    hD K A A ij.1 ij.2 (m ij).hom
  let W : Set Gal := (K.fixingSubgroup : Set Gal) ∩ ⋂ ij, (U ij : Set Gal)
  have hWo : IsOpen W :=
    (IntermediateField.fixingSubgroup_isOpen K).inter (isOpen_iInter_of_finite fun ij => hUo ij)
  have hW1 : (1 : Gal) ∈ W :=
    ⟨K.fixingSubgroup.one_mem, Set.mem_iInter.mpr fun ij => (U ij).one_mem⟩
  have hWS : W ⊆ (stabSub K A m : Set Gal) := by
    rintro σ ⟨hσK, hσU⟩
    rw [Set.mem_iInter] at hσU
    show conjAction K A σ m = m
    rw [conjAction_apply]
    funext ij
    obtain ⟨i, j⟩ := ij
    apply AbVar.Hom.ext'
    rw [conjAct_apply, conjHom_hom]
    have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
        (hf : specEmb K i = specGal σ ≫ specEmb K i')
        (hg : specEmb K j = specGal σ ≫ specEmb K j'),
        G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
      intro i' j' hi hj hf hg
      subst hi hj
      exact hU (i', j') σ (hσU (i', j')) hf hg
    exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _
  have hS : IsOpen (stabSub K A m : Set Gal) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hWo.mem_nhds hW1) hWS)
  exact hS

/-- **G4 for a model `A/K`, continuity discharged.** As `homField_of_model`, with `hcont`
replaced by the input `HomDescends`. -/
theorem homField_of_model' (hHFF : HomFreeFinite) (hD : HomDescends) [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model K hHFF hKF A hdim (conjAction_continuous K hD A) T hK hinert



/-- **G4 for a model `A/K`, final form.** Leaves: `PkgI3.HomFreeFinite` (Mumford §19 Thm 3) and
`MorphismsDescend` (EGA IV₃ 8.8.2). Remaining hypotheses: `hdim` (dimension of base change),
`hK` (G2's output) and `hinert` (inertia outside `T` trivial on the lattice: NOS + the action on
Tate modules, see `inertia_of_tate`). -/
theorem homField_of_model_final (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model' K hHFF (homDescends_of_morphismsDescend hM) hKF A hdim T hK hinert

/-! ### Inertia from good reduction

`InertiaFixesHoms` is the input: at a place `w` of `ℚ̄` where both varieties have good reduction,
inertia fixes every homomorphism between their base changes. It is a consequence of
Néron–Ogg–Shafarevich (Serre–Tate 1968, Thm 1: inertia acts trivially on `T_ℓ` for `ℓ ≠ p`; the
leaf `PkgI2.NeronOggShafarevich`) and the faithfulness of the `ℓ`-adic realization (Mumford §19
Thm 3; `tateHom_injective` above), through the equivariance of the realization under
conjugation. That equivariance is glue that is not formalized here. Stated over the genuine
objects (`PkgI2.HasGoodReduction`, `inertiaGQ`, `G4Conj.conj`). -/

/-- **Input (Serre–Tate 1968 Thm 1 + Mumford §19 Thm 3 + equivariance; derivation not
formalized).** -/
def InertiaFixesHoms : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : (CategoryTheory.Over.pullback (specEmb K e₁)).obj A.X ⟶
      (CategoryTheory.Over.pullback (specEmb K e₂)).obj B.X)
    (w : ValuationSubring Qbar),
    PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e₁ : K →+* Qbar)) →
    PkgI2.HasGoodReduction (ObjBridge.toGrp B) (w.comap (e₂ : K →+* Qbar)) →
    ∀ s ∈ inertiaGQ w, ∀ (hf : specEmb K e₁ = specGal s ≫ specEmb K e₁)
      (hg : specEmb K e₂ = specGal s ≫ specEmb K e₂),
      G4Conj.conj A.X B.X (specGal s) hf hg φ = φ

/-- **The inertia hypothesis of G4 (glue, proved from `InertiaFixesHoms`).** If `K` is unramified
outside `T` and `A` has good reduction at every place of `K` above every `p ∉ T` (G3's output),
inertia above `p ∉ T` acts trivially on the Hom lattice of the conjugates. -/
theorem conjAction_inertia (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1 := by
  intro p hp hpT w hw
  intro (σ : Gal) (hσ : σ ∈ inertiaGQ w)
  have hσK : σ ∈ K.fixingSubgroup := hK p hp hpT w hw hσ
  apply LinearEquiv.ext
  intro m
  show conjAct K A σ m = m
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
      (hf : specEmb K i = specGal σ ≫ specEmb K i')
      (hg : specEmb K j = specGal σ ≫ specEmb K j'),
      G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
    intro i' j' hi hj hf hg
    subst hi hj
    exact hI K A A i' j' (m (i', j')).hom w (hgood p hp hpT w hw i') (hgood p hp hpT w hw j')
      σ hσ hf hg
  exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _

/-- **G4 for a model `A/K`, all analytic inputs as leaves.** Leaves/inputs: `HomFreeFinite`
(Mumford §19 Thm 3), `MorphismsDescend` (EGA IV₃ 8.8.2), `InertiaFixesHoms` (Serre–Tate +
Mumford + equivariance). Hypotheses from other glue steps: `hK` (G2), `hgood` (G3), `hdim`
(dimension of base change, missing from Mathlib). -/
theorem homField_of_model_leaves (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_final K hHFF hM hKF A hdim T hK (conjAction_inertia K hI A T hK hgood)

end Lattice

/-! ## What G7 receives: the Hom field feeds `GlueDescent.B3Q.b3_degree_le_QM`

`b3_degree_le_QM` needs a finite Galois `L` with `[L:ℚ] ≤ D`, unramified outside `T = ramSet S u`
(ideal-theoretic form), and the cocycle `ε` of the scalar descent data inflated from `Gal(L/ℚ)`.
The first three are G4's output above; the last is G7's own instantiation (the descent data
`μ_σ` are elements of the lattice, so a field defining the lattice defines `ε`), kept here as the
hypothesis `hdesc`. -/

section Feed

/-- **G4 → G7.** The Hom field of `homField_le_heightD`, with `T = ramSet S u`, is a valid input
of `GlueDescent.B3Q.b3_degree_le_QM`: the scalar-descent output (`χ`, `β`, `L' ⊇ L` Galois with
`[L':ℚ] ≤ Q_R·M_S(u)`) follows. -/
theorem b3_of_homField (hHasse : GlueDescent.B2Q.LeafHasse)
    (hTwo : GlueDescent.B2Q.LeafLocalTwo) (hSq : GlueDescent.B2Q.LeafSqrtCrit)
    (hUnr : GlueDescent.B2Q.LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ) {M : Type*} [AddCommGroup M]
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    {r : ℕ} (hr : r ≤ 16 * ZInQ.heightF0 ^ 2) (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M))
    (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (hK : GalUnramifiedOutside K (GlueDescent.ramSet S u))
    (hinert : ∀ p : ℕ, p.Prime → p ∉ GlueDescent.ramSet S u → ∀ w : ValuationSubring Qbar,
      LiesOver w p → ∀ s ∈ inertiaGQ w, ρ s = 1)
    (hdesc : ∀ L : IntermediateField ℚ Qbar, (∀ σ ∈ L.fixingSubgroup, ρ σ = 1) →
      ∃ ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ, GlueDescent.B2.IsSignCocycle ε ∧
        GlueDescent.B2Q.InflatedFrom L ε ∧ ε 1 1 = 1)
    (η : GlueDescent.B2Q.GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (L : IntermediateField ℚ Qbar) (ε : GlueDescent.B2Q.GQ → GlueDescent.B2Q.GQ → ℂˣ)
      (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GlueDescent.B2Q.GQ → ℂˣ)
      (L' : IntermediateField ℚ Qbar),
      Module.finrank ℚ L ≤ ZInQ.heightD ∧ K ≤ L ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = GlueDescent.B2Q.galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  obtain ⟨L, hfd, hgal, hKL, hdef, hdeg, -, hram⟩ :=
    homField_le_heightD K hKF hr b ρ hcont (GlueDescent.ramSet S u) hK hinert
  obtain ⟨ε, hε, hinf, h11⟩ := hdesc L hdef
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', -, hdeg'⟩ :=
    GlueDescent.B3Q.b3_degree_le_QM hHasse hTwo hSq hUnr S hS R hRD hRS hR12 u L hdeg ε hε hinf
      h11 hram η hη hηl
  exact ⟨L, ε, N, hN, χ, β, L', hdeg, hKL, hβl, hβs, hβe, hle, hfd', hgal', hdeg'⟩

/-- **G4 → the CM branch.** `GlueAssembly.CMOutput` takes `d = [L:ℚ]` with `1 ≤ d ≤ D` (reals);
the Hom field supplies it. -/
theorem cm_degree_of_homField (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L]
    (hL : Module.finrank ℚ L ≤ ZInQ.heightD) :
    (1 : ℝ) ≤ (Module.finrank ℚ L : ℝ) ∧ (Module.finrank ℚ L : ℝ) ≤ (ZInQ.heightD : ℝ) :=
  ⟨by exact_mod_cast Module.finrank_pos, by exact_mod_cast hL⟩


end Feed

end G4WeilRes


section NewConj

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace G4Conj

variable {C : Type*} [Category C] [HasPullbacks C] {S T : C}

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory


section Agree

variable (X Y : Over S) {f g : T ⟶ S} (s : T ⟶ T) (hf : f = s ≫ f) (hg : g = s ≫ g)

/-- **Equivariance on test points.** If a test point `Q : Z → X_f` and its image `Q ≫ φ` are
fixed by conjugation (relative to a lift `s'` of `s` on `Z`), then `σφ` and `φ` agree on `Q`. -/
theorem conj_agree (φ : (Over.pullback f).obj X ⟶ (Over.pullback g).obj Y) {Z : C}
    (Q : Z ⟶ pullback X.hom f) (s' : Z ⟶ Z)
    (hQ : Q ≫ cmp X s hf = s' ≫ Q)
    (hφQ : (Q ≫ φ.left) ≫ cmp Y s hg = s' ≫ Q ≫ φ.left) :
    Q ≫ (conj X Y s hf hg φ).left = Q ≫ φ.left := by
  rw [Category.assoc] at hφQ
  apply pullback.hom_ext
  · have e1 : Q ≫ (conj X Y s hf hg φ).left ≫ pullback.fst Y.hom g =
        Q ≫ (conj X Y s hf hg φ).left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    have e2 : Q ≫ φ.left ≫ pullback.fst Y.hom g =
        Q ≫ φ.left ≫ cmp Y s hg ≫ pullback.fst Y.hom g := by
      rw [cmp_fst]
    rw [Category.assoc, Category.assoc, e1, e2, conj_cmp_assoc, reassoc_of% hQ,
      reassoc_of% hφQ]
  · rw [Category.assoc, Category.assoc]
    have h1 : (conj X Y s hf hg φ).left ≫ pullback.snd Y.hom g = pullback.snd X.hom f :=
      Over.w _
    have h2 : φ.left ≫ pullback.snd Y.hom g = pullback.snd X.hom f := Over.w φ
    rw [h1, h2]

/-- A section `Q` of `X_f` is fixed by conjugation iff its `X`-component is fixed by `s`. -/
theorem cmp_fixed_of_fst (Q : T ⟶ pullback X.hom f) (hQ : Q ≫ pullback.snd X.hom f = 𝟙 T)
    (h : s ≫ Q ≫ pullback.fst X.hom f = Q ≫ pullback.fst X.hom f) :
    Q ≫ cmp X s hf = s ≫ Q := by
  apply pullback.hom_ext
  · rw [Category.assoc, cmp_fst, Category.assoc, h]
  · rw [Category.assoc, cmp_snd, reassoc_of% hQ, Category.assoc, hQ]
    simp

end Agree

section Sections

variable (X : Over S) [MonObj X] (f : T ⟶ S)

/-- The `X`-component of a section of `X_f`, as a point of `X` over `S` with source `T` (via `f`). -/
noncomputable def secFst (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) : Over.mk f ⟶ X :=
  Over.homMk (Q.left ≫ pullback.fst X.hom f) (by
    rw [Category.assoc, pullback.condition]
    have hw : Q.left ≫ pullback.snd X.hom f = 𝟙 T := Over.w Q
    rw [reassoc_of% hw]
    simp)

omit [MonObj X] in
@[simp] theorem secFst_left (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    (secFst X f Q).left = Q.left ≫ pullback.fst X.hom f := rfl

theorem secFst_mul (Q R : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) :
    secFst X f (Q * R) = secFst X f Q * secFst X f R := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, Category.assoc,
    mul_left_fst, ← Category.assoc]
  congr 1
  rw [Over.lift_left, Over.lift_left]
  apply pullback.hom_ext
  · simp
  · simp

theorem secFst_one : secFst X f (1 : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) = 1 := by
  apply Over.OverMorphism.ext
  rw [secFst_left, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc,
    one_left_fst, Over.toUnit_left, Over.toUnit_left]
  simp

/-- `secFst` as a monoid homomorphism. -/
noncomputable def secFstHom : (Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) →* (Over.mk f ⟶ X) where
  toFun := secFst X f
  map_one' := secFst_one X f
  map_mul' := secFst_mul X f

theorem secFst_pow (Q : Over.mk (𝟙 T) ⟶ (Over.pullback f).obj X) (n : ℕ) :
    secFst X f (Q ^ n) = secFst X f Q ^ n :=
  map_pow (secFstHom X f) Q n

end Sections

end G4Conj

end NewConj

namespace InertiaHoms

open GlueB3Unram
open scoped Pointwise

/-! ## Inertia membership in terms of the valuation subring alone -/

section InertiaChar

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- `v_w(x) < 1` in terms of membership only. -/
theorem valuation_lt_one_iff_mem (w : ValuationSubring L) (x : L) :
    w.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ w := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [hx, false_or]
    rw [← w.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx), inv_inv]

/-- **Inertia, elementwise.** `σ` lies in the inertia group of `w` (Mathlib's
`decompositionSubgroup`/`inertiaSubgroup`) iff `σ` preserves `w` and `σ x - x` lies in the
maximal ideal of `w` for every `x ∈ w` (the latter written by membership only). -/
theorem isInertia_iff (w : ValuationSubring L) (σ : L ≃ₐ[F] L) :
    (∃ h : σ ∈ w.decompositionSubgroup F, (⟨σ, h⟩ : w.decompositionSubgroup F) ∈
        w.inertiaSubgroup F) ↔
      (∀ x, σ x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, σ x - x = 0 ∨ (σ x - x)⁻¹ ∉ w) := by
  have hinv : ∀ x, σ⁻¹ (σ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
  have hinv' : ∀ x, σ (σ⁻¹ x) = x := fun x => by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl
  constructor
  · rintro ⟨h, hin⟩
    have hstab : σ • w = w := h
    have hmem : ∀ y, y ∈ w ↔ σ⁻¹ y ∈ w := fun y => by
      conv_lhs => rw [← hstab]
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    have hD : ∀ x, σ x ∈ w ↔ x ∈ w := fun x => by rw [hmem (σ x), hinv]
    refine ⟨hD, fun x hx => ?_⟩
    rw [← valuation_lt_one_iff_mem]
    have hk := congrArg (fun φ : RingAut (IsLocalRing.ResidueField w) =>
      φ (IsLocalRing.residue w ⟨x, hx⟩)) (MonoidHom.mem_ker.mp hin)
    simp only [RingAut.one_apply, MulSemiringAction.toRingAut_apply] at hk
    change (⟨σ, h⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w ⟨x, hx⟩ = _ at hk
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hk
    exact hk
  · rintro ⟨hD, hI⟩
    have hstab : σ • w = w := by
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hD, hinv']
    have hdec : σ ∈ w.decompositionSubgroup F := hstab
    refine ⟨hdec, ?_⟩
    unfold ValuationSubring.inertiaSubgroup
    rw [MonoidHom.mem_ker]
    apply RingEquiv.ext
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨σ, hdec⟩ : w.decompositionSubgroup F) • IsLocalRing.residue w a =
      IsLocalRing.residue w a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    rw [valuation_lt_one_iff_mem]
    exact hI a.1 a.2

end InertiaChar

section Transport

/-- **Inertia transports along a ring isomorphism.** If `s` satisfies the elementwise inertia
conditions at `w`, then `ι⁻¹ ∘ s ∘ ι` satisfies them at `w.comap ι`. -/
theorem inertia_transport {L₁ L₂ : Type*} [Field L₁] [Field L₂] (ι : L₁ ≃+* L₂)
    (w : ValuationSubring L₂) (s : L₂ ≃+* L₂)
    (hD : ∀ x, s x ∈ w ↔ x ∈ w) (hI : ∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) :
    (∀ x, ι.symm (s (ι x)) ∈ w.comap (ι : L₁ →+* L₂) ↔ x ∈ w.comap (ι : L₁ →+* L₂)) ∧
      (∀ x ∈ w.comap (ι : L₁ →+* L₂), ι.symm (s (ι x)) - x = 0 ∨
        (ι.symm (s (ι x)) - x)⁻¹ ∉ w.comap (ι : L₁ →+* L₂)) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · simp only [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact hD _
  · rw [ValuationSubring.mem_comap] at hx
    have key : ι (ι.symm (s (ι x)) - x) = s (ι x) - ι x := by
      rw [map_sub, RingEquiv.apply_symm_apply]
    rcases hI _ hx with h | h
    · left
      apply ι.injective
      have h' : s (ι x) - ι x = 0 := h
      rw [key, h', map_zero]
    · right
      rw [ValuationSubring.mem_comap, RingEquiv.coe_toRingHom, map_inv₀, key]
      exact h

end Transport

section Closure

/-- `ℚ̄` is an algebraic closure of `K` through any embedding `e : K → ℚ̄`: a ring isomorphism
`ι : K̄ ≃ ℚ̄` extending `e`. -/
theorem exists_closure_equiv (K : IntermediateField ℚ Qbar) (e : K →ₐ[ℚ] Qbar) :
    ∃ ι : AlgebraicClosure K ≃+* Qbar, ∀ x, ι (algebraMap K (AlgebraicClosure K) x) = e x := by
  let R : IntermediateField ℚ Qbar := e.fieldRange
  let hSR : K ≃+* R := (AlgEquiv.ofInjectiveField e).toRingEquiv
  have : Algebra.IsAlgebraic R Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) R
  have : IsAlgClosure R Qbar := ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv (AlgebraicClosure K) Qbar hSR, fun x => ?_⟩
  rw [IsAlgClosure.equivOfEquiv_algebraMap]
  rfl

end Closure

section Unit

/-- At a place over `p`, every prime `ℓ ≠ p` is a unit of the valuation ring (of any subfield). -/
theorem isUnit_prime_of_liesOver {F : Type*} [Field F] [CharZero F] (f : F →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hne : ℓ ≠ p) : IsUnit ((ℓ : ℕ) : w.comap f) := by
  have hcop : IsCoprime (ℓ : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hℓ hp).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop
  have hpw : ((p : w) : Qbar) = p := by simp
  have hℓw : ((ℓ : w) : Qbar) = ℓ := by simp
  have hpm : (p : w) ∈ IsLocalRing.maximalIdeal w := by
    rw [ValuationSubring.valuation_lt_one_iff, hpw]; exact hw
  have hv1 : w.valuation (ℓ : Qbar) = 1 := by
    rcases w.valuation_lt_one_or_eq_one (ℓ : w) with h | h
    · exfalso
      have hℓm : (ℓ : w) ∈ IsLocalRing.maximalIdeal w := by
        rw [ValuationSubring.valuation_lt_one_iff]; exact h
      have h1 : (1 : w) ∈ IsLocalRing.maximalIdeal w := by
        have : ((a : w) * (ℓ : w) + (b : w) * (p : w)) = 1 := by
          have := congrArg (Int.cast : ℤ → w) hab
          push_cast at this
          exact this
        rw [← this]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓm) (Ideal.mul_mem_left _ _ hpm)
      exact (IsLocalRing.maximalIdeal.isMaximal w).ne_top
        ((Ideal.eq_top_iff_one _).mpr h1)
    · rw [← hℓw]; exact h
  have hℓF : (ℓ : F) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  have hinv : (ℓ : F)⁻¹ ∈ w.comap f := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast, ← w.valuation_le_one_iff, map_inv₀,
      hv1, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨(ℓ : F)⁻¹, hinv⟩, ?_⟩
  apply Subtype.ext
  simp [hℓF]

end Unit

section DVR

open NumberField IsDedekindDomain

/-- Algebraic integers lie in every valuation subring of `ℚ̄`. -/
theorem mem_of_isIntegral_int (w : ValuationSubring Qbar) (y : Qbar) (hy : IsIntegral ℤ y) :
    y ∈ w := by
  have hv := Valuation.valuationSubring.integers w.valuation
  have hy' : IsIntegral w.valuation.valuationSubring y := hy.tower_top
  exact (w.valuation_le_one_iff y).mp (hv.isIntegral_iff_v_le_one.mp hy')

/-- **A place of `ℚ̄` over `p` restricts to a DVR on every number field (glue, proved).** The
restriction `O = w ∩ F` contains `𝓞_F`; with `P = 𝔪_O ∩ 𝓞_F` (a nonzero prime, `p ∈ P`), the
`P`-adic valuation ring `𝓞_{F,P}` (Mathlib: a DVR) is contained in `O`, and `O ≠ F`, so
`O = 𝓞_{F,P}` (a valuation ring of Krull dimension `1` has no proper overrings but `F`). -/
theorem comap_isDVR {F : Type*} [Field F] [NumberField F] (f : F →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p) :
    IsDiscreteValuationRing (w.comap f) := by
  set Ov := w.comap f with hOv
  have hint : ∀ x : 𝓞 F, algebraMap (𝓞 F) F x ∈ Ov := fun x => by
    rw [ValuationSubring.mem_comap]
    exact mem_of_isIntegral_int w _ ((RingOfIntegers.isIntegral_coe x).map f.toIntAlgHom)
  let ι0 : 𝓞 F →+* Ov := (algebraMap (𝓞 F) F).codRestrict Ov.toSubring hint
  have hι0 : ∀ x, ((ι0 x : Ov) : F) = algebraMap (𝓞 F) F x := fun x => rfl
  let P : Ideal (𝓞 F) := (IsLocalRing.maximalIdeal Ov).comap ι0
  have hPp : P.IsPrime := Ideal.comap_isPrime _ _
  have hpinv : ((p : F))⁻¹ ∉ Ov := by
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]
    rcases (valuation_lt_one_iff_mem w (p : Qbar)).mp hw with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne_zero)
    · exact h
  have hmax : ∀ x : 𝓞 F, x ∈ P ↔ algebraMap (𝓞 F) F x = 0 ∨
      (algebraMap (𝓞 F) F x)⁻¹ ∉ Ov := fun x => by
    show ι0 x ∈ IsLocalRing.maximalIdeal Ov ↔ _
    rw [ValuationSubring.valuation_lt_one_iff, valuation_lt_one_iff_mem, hι0]
  have hpP : ((p : 𝓞 F)) ∈ P := by
    rw [hmax]
    right
    simpa using hpinv
  have hPne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hpP
    exact hp.ne_zero (by exact_mod_cast hpP)
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hPp, hPne⟩
  have hle : (v.valuation F).valuationSubring ≤ Ov := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x hx
    have hdP : (d : 𝓞 F) ∉ P := d.2
    have hdu : IsUnit (ι0 d) := by
      by_contra h
      exact hdP ((IsLocalRing.mem_maximalIdeal _).mpr h)
    have hd0 : algebraMap (𝓞 F) F d ≠ 0 := by
      intro h0
      apply hdP
      rw [hmax]
      left
      exact h0
    obtain ⟨u, hu⟩ := hdu
    have hinvmem : (algebraMap (𝓞 F) F d)⁻¹ ∈ Ov := by
      have h1 : ((u⁻¹ : Ovˣ) : Ov) * (u : Ov) = 1 := by simp
      have h2 : (((u⁻¹ : Ovˣ) : Ov) : F) * algebraMap (𝓞 F) F d = 1 := by
        rw [← hι0, ← hu]
        exact_mod_cast congrArg (fun t : Ov => (t : F)) h1
      have h3 : (((u⁻¹ : Ovˣ) : Ov) : F) = (algebraMap (𝓞 F) F d)⁻¹ :=
        eq_inv_of_mul_eq_one_left h2
      rw [← h3]
      exact ((u⁻¹ : Ovˣ) : Ov).2
    have hx : x = algebraMap (𝓞 F) F n * (algebraMap (𝓞 F) F d)⁻¹ := by
      rw [← hnd, mul_assoc, mul_inv_cancel₀ hd0, mul_one]
    rw [hx]
    exact Ov.mul_mem _ _ (hint n) hinvmem
  have hne : Ov ≠ ⊤ := fun h => hpinv (by rw [h]; exact ValuationSubring.mem_top _)
  haveI : IsDiscreteValuationRing (v.valuation F).valuationSubring :=
    (inferInstance : IsDiscreteValuationRing (v.valuation F).integer)
  have heq : (v.valuation F).valuationSubring = Ov :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hne
  rw [← heq]
  infer_instance

end DVR

end InertiaHoms



namespace G4WeilRes

open GlueB3Unram CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms

variable (K : IntermediateField ℚ Qbar)


theorem specMap_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (a : R →+* S)
    (b : S →+* U) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (b.comp a)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- **Inertia fixes prime-to-`p` torsion points of a conjugate (NOS, transported).** Let `A/K`
have good reduction at `w ∩ e(K)` (a DVR), `s ∈ I_w` fix `e(K)`, and `m` be invertible at `w`.
A point `q : Spec ℚ̄ → A` over `Spec e` with `q^m = 1` is fixed by `s`: `Spec s ≫ q = q`.
Leaf: `PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1), applied to `A/K` at `w ∩ e(K)`, with
`ℚ̄ ≅ K̄` extending `e` and the inertia group transported along it. -/
theorem point_fixed (hNOS : PkgI2.NeronOggShafarevich.{0})
    (A : AbVar K) (e : K →ₐ[ℚ] Qbar) (w : ValuationSubring Qbar)
    [IsDiscreteValuationRing (w.comap (e : K →+* Qbar))]
    (hgood : PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar)))
    (s : Gal) (hs : s ∈ inertiaGQ w) (hse : ∀ x, s (e x) = e x)
    (m : ℕ) (hm : 0 < m) (hmO : IsUnit ((m : ℕ) : w.comap (e : K →+* Qbar)))
    (q : CategoryTheory.Over.mk (specEmb K e) ⟶ A.X) (hq : q ^ m = 1) :
    specGal s ≫ q.left = q.left := by
  obtain ⟨ie, hie⟩ := exists_closure_equiv K e
  have hies : ∀ x : K, ie.symm (e x) = algebraMap K (AlgebraicClosure K) x := fun x => by
    rw [← hie, RingEquiv.symm_apply_apply]
  let σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofRingEquiv (f := (ie.trans s.toRingEquiv).trans ie.symm) (fun x => by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, hie, hse, hies])
  have hσ : ∀ x, σ x = ie.symm (s (ie x)) := fun x => rfl
  let w' : ValuationSubring (AlgebraicClosure K) := w.comap (ie : AlgebraicClosure K →+* Qbar)
  have hw' : w'.comap (algebraMap K (AlgebraicClosure K)) = w.comap (e : K →+* Qbar) := by
    ext x
    simp only [w', ValuationSubring.mem_comap, RingEquiv.coe_toRingHom]
    rw [hie]
    rfl
  have hsI : (∀ x, s x ∈ w ↔ x ∈ w) ∧ (∀ x ∈ w, s x - x = 0 ∨ (s x - x)⁻¹ ∉ w) := by
    obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp hs
    have := (isInertia_iff w g.1).mp ⟨g.2, hg⟩
    rw [← hgs]
    exact this
  have hIσ : PkgI2.IsInertia w' σ := by
    rw [PkgI2.IsInertia, isInertia_iff]
    exact inertia_transport ie w s.toRingEquiv hsI.1 hsI.2
  let J : PkgI2.specOver K (AlgebraicClosure K) ⟶ CategoryTheory.Over.mk (specEmb K e) :=
    CategoryTheory.Over.homMk
      (Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K))) (by
        show Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [specMap_comp]
        congr 2
        ext x
        exact hies x)
  let x : PkgI2.Pts (ObjBridge.toGrp A) (AlgebraicClosure K) := J ≫ q
  have hx : x ∈ PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure K) m := by
    show (J ≫ q) ^ m = 1
    rw [← MonObj.comp_pow, hq, MonObj.comp_one]
  have hfix := ((hNOS K (w.comap (e : K →+* Qbar)) w' hw' (ObjBridge.toGrp A)).1.mp hgood)
    m hm hmO σ hIσ x hx
  have h2 : Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left =
      Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      Spec.map (CommRingCat.ofHom (ie.symm : Qbar →+* AlgebraicClosure K)) ≫ q.left := by
    have := congrArg (fun t => Spec.map (CommRingCat.ofHom (ie : AlgebraicClosure K →+* Qbar)) ≫
      CategoryTheory.Over.Hom.left t) hfix
    exact this
  rw [← Category.assoc, ← Category.assoc, specMap_comp, specMap_comp, ← Category.assoc,
    specMap_comp] at h2
  have e1 : ((ie : AlgebraicClosure K →+* Qbar).comp
      (σ : AlgebraicClosure K →+* AlgebraicClosure K)).comp
      (ie.symm : Qbar →+* AlgebraicClosure K) = (s : Qbar →+* Qbar) := by
    ext y
    simp [hσ]
  have e2 : (ie : AlgebraicClosure K →+* Qbar).comp (ie.symm : Qbar →+* AlgebraicClosure K) =
      RingHom.id Qbar := by
    ext y
    simp
  rw [e1, e2] at h2
  rw [h2, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

/-- A point `P` of `X ×_{K,e} ℚ̄` with values in `L = AlgebraicClosure ℚ̄` (the points used by
`PkgI3.AbVar.T`) factors through the section `J' ≫ P` over `Spec ℚ̄`, because `ℚ̄ → L` is an
isomorphism. -/
noncomputable def ptIso :
    PkgI3.AbVar.ptObj (K := Qbar) (AlgebraicClosure Qbar) ≅
      CategoryTheory.Over.mk (𝟙 (Spec (CommRingCat.of Qbar))) := by
  let ie : Qbar ≃+* AlgebraicClosure Qbar := RingEquiv.ofBijective
    (algebraMap Qbar (AlgebraicClosure Qbar))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Qbar) (K := AlgebraicClosure Qbar))
  have h1 : (ie.symm : AlgebraicClosure Qbar →+* Qbar).comp
      (algebraMap Qbar (AlgebraicClosure Qbar)) = RingHom.id Qbar := by
    ext y
    exact ie.symm_apply_apply y
  have h2 : (algebraMap Qbar (AlgebraicClosure Qbar)).comp
      (ie.symm : AlgebraicClosure Qbar →+* Qbar) = RingHom.id _ := by
    ext y
    exact ie.apply_symm_apply y
  refine
    { hom := CategoryTheory.Over.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap Qbar (AlgebraicClosure Qbar)))) (by simp [PkgI3.AbVar.ptObj])
      inv := CategoryTheory.Over.homMk
        (Spec.map (CommRingCat.ofHom (ie.symm : AlgebraicClosure Qbar →+* Qbar))) (by
          show _ ≫ Spec.map _ = 𝟙 _
          rw [specMap_comp, h1, CommRingCat.ofHom_id, Spec.map_id])
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply CategoryTheory.Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [specMap_comp, h2, CommRingCat.ofHom_id, Spec.map_id]
  · apply CategoryTheory.Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [specMap_comp, h1, CommRingCat.ofHom_id, Spec.map_id]

/-- **The corrected input** (homomorphisms only, at a place over a prime). -/
def InertiaFixesHomsMon : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (A B : AbVar K)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : AbVar.Hom (bcAlong A (e₁ : K →+* Qbar)) (bcAlong B (e₂ : K →+* Qbar)))
    (w : ValuationSubring Qbar) (p : ℕ), p.Prime → LiesOver w p →
    PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e₁ : K →+* Qbar)) →
    PkgI2.HasGoodReduction (ObjBridge.toGrp B) (w.comap (e₂ : K →+* Qbar)) →
    ∀ s ∈ inertiaGQ w, ∀ (hf : specEmb K e₁ = specGal s ≫ specEmb K e₁)
      (hg : specEmb K e₂ = specGal s ≫ specEmb K e₂),
      G4Conj.conj A.X B.X (specGal s) hf hg φ.hom = φ.hom

/-- **Glue Prop: valuation rings of number fields are DVRs** (standard; see `isDVR_comap`). -/
def ComapDVR : Prop :=
  ∀ (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] (f : K →+* Qbar)
    (w : ValuationSubring Qbar) (p : ℕ), p.Prime → LiesOver w p →
    IsDiscreteValuationRing (w.comap f)

theorem fixes_of_spec (s : Gal) (e : K →ₐ[ℚ] Qbar) (h : specEmb K e = specGal s ≫ specEmb K e) :
    ∀ x, s (e x) = e x := by
  intro x
  have h' := Spec.map_injective (h.trans (specMap_comp _ _))
  have := congrArg (fun φ => (CommRingCat.Hom.hom φ) x) h'
  exact this.symm

/-- **`InertiaFixesHomsMon` from NOS and Mumford §19 Thm 3 (glue, proved).** -/
theorem inertiaFixesHomsMon (hNOS : PkgI2.NeronOggShafarevich.{0}) (hHFF : HomFreeFinite)
    (hDVR : ComapDVR) : InertiaFixesHomsMon := by
  intro K _ A B e₁ e₂ φ w p hp hw hA hB s hs hf hg
  have := hDVR K (e₁ : K →+* Qbar) w p hp hw
  have := hDVR K (e₂ : K →+* Qbar) w p hp hw
  -- an auxiliary prime `ℓ ≠ p`
  obtain ⟨ℓ, hℓ, hℓp⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
    by_cases h2 : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, fun h => h2 h.symm⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hse₁ := fixes_of_spec K s e₁ hf
  have hse₂ := fixes_of_spec K s e₂ hg
  have hunit : ∀ (e : K →ₐ[ℚ] Qbar) (n : ℕ),
      IsUnit (((ℓ ^ n : ℕ) : ℕ) : w.comap (e : K →+* Qbar)) := fun e n => by
    rw [Nat.cast_pow]
    exact (isUnit_prime_of_liesOver (e : K →+* Qbar) w p hp hw ℓ hℓ hℓp).pow n
  let A₁ := bcAlong A (e₁ : K →+* Qbar)
  let B₂ := bcAlong B (e₂ : K →+* Qbar)
  let ψ : A₁.X ⟶ B₂.X := G4Conj.conj A.X B.X (specGal s) hf hg φ.hom
  have hψ : IsMonHom ψ :=
    G4Conj.conj_isMonHom' A.X B.X (specGal s) hf hg φ.hom (show IsMonHom φ.hom from inferInstance)
  -- agreement on torsion sections over `Spec ℚ̄`
  have hsec : ∀ (n : ℕ) (Q : CategoryTheory.Over.mk (𝟙 (Spec (CommRingCat.of Qbar))) ⟶ A₁.X),
      Q ^ (ℓ ^ n) = 1 → Q.left ≫ ψ.left = Q.left ≫ φ.hom.left := by
    intro n Q hQ
    have hfixA : Q.left ≫ G4Conj.cmp A.X (specGal s) hf = specGal s ≫ Q.left := by
      apply G4Conj.cmp_fixed_of_fst A.X (specGal s) hf Q.left (CategoryTheory.Over.w Q)
      have hq : G4Conj.secFst A.X (specEmb K e₁) Q ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow A.X (specEmb K e₁) Q (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst A.X (specEmb K e₁)) hQ).trans (G4Conj.secFst_one _ _))
      have := point_fixed K hNOS A e₁ w hA s hs hse₁ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₁ n)
        (G4Conj.secFst A.X (specEmb K e₁) Q) hq
      exact this
    have hfixB : (Q ≫ φ.hom).left ≫ G4Conj.cmp B.X (specGal s) hg =
        specGal s ≫ (Q ≫ φ.hom).left := by
      apply G4Conj.cmp_fixed_of_fst B.X (specGal s) hg (Q ≫ φ.hom).left (CategoryTheory.Over.w _)
      have hQφ : (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 := by
        rw [← MonObj.pow_comp, hQ, MonObj.one_comp]
      have hq : G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom) ^ (ℓ ^ n) = 1 :=
        (G4Conj.secFst_pow B.X (specEmb K e₂) (Q ≫ φ.hom) (ℓ ^ n)).symm.trans
          ((congrArg (G4Conj.secFst B.X (specEmb K e₂)) hQφ).trans (G4Conj.secFst_one _ _))
      have := point_fixed K hNOS B e₂ w hB s hs hse₂ (ℓ ^ n) (pow_pos hℓ.pos n) (hunit e₂ n)
        (G4Conj.secFst B.X (specEmb K e₂) (Q ≫ φ.hom)) hq
      exact this
    exact G4Conj.conj_agree A.X B.X (specGal s) hf hg φ.hom Q.left (specGal s) hfixA
      hfixB
  -- conclude with Mumford's injectivity into Hom of Tate modules
  have hne : (ℓ : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
  let Ψ : AbVar.Hom A₁ B₂ := @AbVar.Hom.mk' _ _ A₁ B₂ ψ hψ
  have key : tateHom ℓ A₁ B₂ Ψ = tateHom ℓ A₁ B₂ φ := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    have htor : (Additive.toMul (t.1 n)) ^ (ℓ ^ n) = 1 :=
      congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero t.2 n)
    set P := Additive.toMul (t.1 n)
    have hP : (ptIso.inv ≫ P) ^ (ℓ ^ n) = 1 := by
      rw [← MonObj.comp_pow, htor, MonObj.comp_one]
    have h1 := hsec n (ptIso.inv ≫ P) hP
    have hPl : P.left = ptIso.hom.left ≫ (ptIso.inv ≫ P).left :=
      congrArg CategoryTheory.Over.Hom.left (Iso.hom_inv_id_assoc ptIso P).symm
    have h2 : P ≫ ψ = P ≫ φ.hom := by
      apply CategoryTheory.Over.OverMorphism.ext
      show P.left ≫ ψ.left = P.left ≫ φ.hom.left
      rw [hPl, Category.assoc, Category.assoc, h1]
    show Additive.ofMul (P ≫ ψ) = Additive.ofMul (P ≫ φ.hom)
    rw [h2]
  have := tateHom_injective hHFF A₁ B₂ ℓ hne key
  exact congrArg AbVar.Hom.hom this

/-- `ComapDVR` holds (glue, proved: `InertiaHoms.comap_isDVR`). -/
theorem comapDVR : ComapDVR := by
  intro K _ f w p hp hw
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  exact comap_isDVR f w p hp hw

/-- **`InertiaFixesHomsMon` from the two leaves (glue, proved).** Leaves:
`PkgI2.NeronOggShafarevich` (Serre–Tate 1968 Thm 1) and `PkgI3.HomFreeFinite` (Mumford §19
Thm 3). -/
theorem inertiaFixesHomsMon_of_leaves (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hHFF : HomFreeFinite) : InertiaFixesHomsMon :=
  inertiaFixesHomsMon hNOS hHFF comapDVR

end G4WeilRes

namespace G4WeilRes

open GlueB3Unram GlueDescent.B2Q CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms

variable (K : IntermediateField ℚ Qbar)

/-- **The inertia hypothesis of G4 from the corrected input (glue, proved).** As
`conjAction_inertia`, with `InertiaFixesHomsMon` in place of `InertiaFixesHoms`. -/
theorem conjAction_inertia' (hI : InertiaFixesHomsMon) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (A : AbVar K) (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, conjAction K A s = 1 := by
  intro p hp hpT w hw
  intro (σ : Gal) (hσ : σ ∈ inertiaGQ w)
  have hσK : σ ∈ K.fixingSubgroup := hK p hp hpT w hw hσ
  apply LinearEquiv.ext
  intro m
  show conjAct K A σ m = m
  funext ij
  obtain ⟨i, j⟩ := ij
  apply AbVar.Hom.ext'
  rw [conjAct_apply, conjHom_hom]
  have aux : ∀ (i' j' : K →ₐ[ℚ] Qbar) (hi : i' = i) (hj : j' = j)
      (hf : specEmb K i = specGal σ ≫ specEmb K i')
      (hg : specEmb K j = specGal σ ≫ specEmb K j'),
      G4Conj.conj A.X A.X (specGal σ) hf hg (m (i', j')).hom = (m (i, j)).hom := by
    intro i' j' hi hj hf hg
    subst hi hj
    exact hI K A A i' j' (m (i', j')) w p hp hw (hgood p hp hpT w hw i')
      (hgood p hp hpT w hw j') σ hσ hf hg
  exact aux _ _ (embAct_symm_of_mem K σ hσK i) (embAct_symm_of_mem K σ hσK j) _ _

/-- **G4 for a model `A/K`, with the inertia input eliminated.** Leaves: `HomFreeFinite`
(Mumford §19 Thm 3), `MorphismsDescend` (EGA IV₃ 8.8.2), `NeronOggShafarevich` (Serre–Tate 1968
Thm 1). Hypotheses from other glue steps: `hK` (G2), `hgood` (G3), `hdim` (dimension of base
change). -/
theorem homField_of_model_leaves' (hHFF : HomFreeFinite) (hM : MorphismsDescend)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_final K hHFF hM hKF A hdim T hK
    (conjAction_inertia' K (inertiaFixesHomsMon_of_leaves hNOS hHFF) A T hK hgood)

end G4WeilRes
end PartInertia

/-! # Part 3. scratch/morph-descend/G4Closed.lean lines 1867-1897 (verbatim) -/
section PartClosed
namespace G4WeilRes

/-- **`MorphismsDescend` of G4 (EGA IV₃ 8.8.2), proved.** The statement here (over
`GlueB3Unram.Qbar`) is `MorphDescend.MorphismsDescend` (over `MorphDescend.Qbar`); both `Qbar`s
are the reducible abbreviation `AlgebraicClosure ℚ`. -/
theorem morphismsDescend : MorphismsDescend := MorphDescend.morphismsDescend

open GlueB3Unram GlueDescent.B2Q NumberField PkgI3 AlgebraicGeometry

variable (K : IntermediateField ℚ Qbar)

/-- **G4 for a model `A/K`, with `MorphismsDescend` discharged.** Remaining inputs:
`HomFreeFinite` (Mumford §19 Thm 3), `InertiaFixesHoms`; hypotheses `hK` (G2), `hgood` (G3),
`hdim`. -/
theorem homField_of_model_closed (hHFF : HomFreeFinite)
    (hI : InertiaFixesHoms) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0)
    (A : AbVar K) (hdim : ∀ e, ((conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ L : IntermediateField ℚ Qbar, ∃ _ : FiniteDimensional ℚ L, ∃ _ : IsGalois ℚ L,
      K ≤ L ∧ (∀ σ ∈ L.fixingSubgroup, conjAction K A σ = 1) ∧
      Module.finrank ℚ L ≤ ZInQ.heightD ∧
      GalUnramifiedOutside L T ∧ (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :=
  homField_of_model_leaves K hHFF morphismsDescend hI hKF A hdim T hK hgood

/-- `HomDescends` (continuity input of G4), now unconditional. -/
theorem homDescends : HomDescends := homDescends_of_morphismsDescend morphismsDescend

end G4WeilRes
end PartClosed

/-! # Part 4. scratch/g0-dim/Dim.lean lines 107-305 (verbatim, namespace G0Dim) -/
section PartDim
open Order TensorProduct
namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim
end PartDim

/-! # Part 5. scratch/g0-mod-field/ModField.lean lines 17-end (verbatim) -/
section PartModField
/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`A/L` is a QM model of `P`**: the base change to `L` of the abelian surface of an object
`PK` of `Y₃`'s moduli problem (QM by `𝒪` with level-3 structure) over a subfield `K ≤ L`, itself a
model of `P`'s surface. Such an `A` has good reduction away from `3` (G3,
`LeafQM.AV.QML3.goodReduction`), unlike an arbitrary model (a twist by a cocycle ramified at
`p ∉ T` has bad reduction at `p`), so the later steps (G11, G15) hold for every such `A`. -/
def IsQMModel (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (hKL : K ≤ L) (PK : QML3 K), IsModelOver K PK.A P ∧
    A = @PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-! ## The outputs of G2, G4, G7 -/

/-- **G2's output (Lemma PR(i), N5 L524-529).** A finite Galois `K ⊆ ℚ̄` with `[K:ℚ] ≤ F₀ = 324!`,
unramified outside `T`, with a rational fibre `PK/K` over `P` (Glazer: "Choose a fiber `A/K`";
`RationalFibre`). -/
def G2Out (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
    Module.finrank ℚ K ≤ heightF0 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) ∧
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK

/-- `A(ℚ̄)` as an additive group, for `A` over `L ⊆ ℚ̄`. -/
abbrev PtQ (L : IF) (A : PkgI3.AbVar L) : Type := Additive (A.Pt Qbar)

/-- **The descent datum of B1 on the actual `A` (N5 L632-663).** `ε` is a normalized
locally constant sign 2-cocycle of `G_ℚ` inflated from `Gal(L/ℚ)`, and it is the cocycle of `A`:
there are maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` (`μ_σ : ^σA → A` the `B`-linear conjugacy isogeny over
`L`, `σ` acting on coordinates) and reals `a_σ > 0` (`a_σ = (deg μ_σ)^{-1/4}`) with
* `a` inflated from `Gal(L/ℚ)` with `a = 1` on `G_L`,
* `m_σ` the Galois action of `σ` for `σ ∈ G_L` (`μ_σ = 1` there),
* `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L` (`μ` inflated from `Gal(L/ℚ)`, defined
  over `L`),
* `m_σ` commutes with every `L`-endomorphism of `A` (`μ_σ` is `B`-linear and `L` is the Hom
  field),
* `m_σ` surjective with finite kernel (an isogeny composed with a bijection),
* `m_σ m_τ = c(σ,τ) m_{στ}` with `c = n/d ∈ ℚ^×` (the discrepancy commutes with `B`), and
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` (N5 L651-660: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`).
* `m_σ` is algebraic: it is induced by a finite surjective morphism of schemes
  `F_σ : A → A` (`μ_σ`, composed with the identification of the underlying schemes of `^σA` and
  `A`): `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` (G14's trace identities reduce `F_σ` modulo primes).
The maps `m_σ` are on points, hence independent of `ℓ`; on `V_ℓ(A)` they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727). -/
def DescentDatum (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) : Prop :=
  IsSignCocycle ε ∧ InflatedFrom L ε ∧ ε 1 1 = 1 ∧
  ∃ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ),
    (∀ σ, 0 < a σ) ∧
    (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) ∧
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
    (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
    (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
    (∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) ∧
        (((a σ * a τ * ((n : ℝ) / d) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) ∧
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ)

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-- The sign of a rational, as `±1 ∈ ℂ^×` (`1` for `q > 0`). -/
noncomputable def sgnU (q : ℚ) : ℂˣ := if 0 < q then 1 else -1

theorem sgnU_sq (q : ℚ) : sgnU q ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

theorem sgnU_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : sgnU (q * r) = sgnU q * sgnU r := by
  unfold sgnU
  rcases lt_or_gt_of_ne hq with hq' | hq' <;> rcases lt_or_gt_of_ne hr with hr' | hr'
  · rw [if_pos (mul_pos_of_neg_of_neg hq' hr'), if_neg (not_lt.2 hq'.le),
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos hq' hr').le), if_neg (not_lt.2 hq'.le),
      if_pos hr']; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg hq' hr').le), if_pos hq',
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_pos (mul_pos hq' hr'), if_pos hq', if_pos hr']; simp

/-- `sgn(q)·|q| = q`, in `ℂ`. -/
theorem sgnU_mul_abs (q : ℚ) : ((sgnU q : ℂˣ) : ℂ) * ((|(q : ℝ)| : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
  unfold sgnU
  split_ifs with h
  · have : (0 : ℝ) < q := by exact_mod_cast h
    rw [abs_of_pos this]; simp
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    rw [abs_of_nonpos this]; push_cast; ring

/-- **The conjugacy isogenies before normalization (N5 L632-645; the content of G4 + B1's
geometric half).** Maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the first four clauses of
`DescentDatum`; the discrepancy `c(σ,τ) = n/d ∈ ℚ^×` with `d·m_σ m_τ = n·m_{στ}`, a 2-cocycle
inflated from `Gal(L/ℚ)` with `c(1,1) = 1`; and degree multiplicativity in the form
`|ker m_σ|·|ker m_τ| = c(σ,τ)⁴·|ker m_{στ}|` (`deg μ = |ker μ(ℚ̄)|` in characteristic 0,
`deg[n] = n⁴` on a surface); and algebraicity: `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite
surjective scheme morphism `F_σ : A → A`. -/
def ConjugacyData (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A))
    (c : GQ → GQ → ℚ) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, c σ τ ≠ 0 ∧ ∃ n d : ℤ, d ≠ 0 ∧ c σ τ = n / d ∧
      d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∀ σ τ ρ, c (σ * τ) ρ * c σ τ = c τ ρ * c σ (τ * ρ)) ∧
  (∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) →
      c σ τ = c σ' τ') ∧
  c 1 1 = 1 ∧
  (∀ σ τ, (Nat.card (m σ).ker : ℚ) * Nat.card (m τ).ker = c σ τ ^ 4 * Nat.card (m (σ * τ)).ker) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- The Galois action of `σ' ∈ Aut(ℚ̄/L)` on `A(ℚ̄)` is bijective. -/
theorem galAct_bijective {L : IF} (A : PkgI3.AbVar L) (σ' : Qbar ≃ₐ[L] Qbar) :
    Function.Bijective (A.galAct σ') := by
  have key : ∀ (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar),
      A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
    intro g h P
    show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]
  have one : ∀ P : A.Pt Qbar, A.galAct 1 P = P := by
    intro P
    show PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  refine ⟨fun P Q h => ?_, fun Q => ⟨A.galAct σ'⁻¹ Q, ?_⟩⟩
  · have := congrArg (A.galAct σ'⁻¹) h
    rwa [key, key, inv_mul_cancel, one, one] at this
  · rw [key, mul_inv_cancel, one]

/-- `k ∈ G_L` as an `L`-automorphism of `ℚ̄`. -/
noncomputable def toLAut {L : IF} (k : GQ) (hk : k ∈ GQL L) : Qbar ≃ₐ[L] Qbar :=
  AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun x => mem_GQL.mp hk x x.2)

theorem toLAut_apply {L : IF} (k : GQ) (hk : k ∈ GQL L) (x : Qbar) : toLAut k hk x = act k x :=
  rfl

/-- The kernel sizes of `m_k`, `m_{σk}`, `m_{kσ}` for `k ∈ G_L` (from the first two clauses of
`ConjugacyData`). -/
theorem card_ker_GL {L : IF} {A : PkgI3.AbVar L} {m : GQ → (PtQ L A →+ PtQ L A)}
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (σ k : GQ) (hk : k ∈ GQL L) :
    Nat.card (m k).ker = 1 ∧ Nat.card (m (σ * k)).ker = Nat.card (m σ).ker ∧
      Nat.card (m (k * σ)).ker = Nat.card (m σ).ker := by
  have hmk : m k = MonoidHom.toAdditive (A.galAct (toLAut k hk)) :=
    hgal k (toLAut k hk) (toLAut_apply k hk)
  have hbij : Function.Bijective (m k) := by
    rw [hmk]; exact galAct_bijective A (toLAut k hk)
  have hker : (m k).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : m k x = m k 0 := by rw [map_zero]; exact hx
    exact hbij.1 this
  refine ⟨by rw [hker]; simp, ?_, ?_⟩
  · rw [(hinfl σ k hk).1]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨m k x, x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hbij.1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨⟨x, hy⟩, rfl⟩
  · have hk2 : ((m k).comp (m σ)).ker = (m σ).ker := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      constructor
      · intro h
        have : m k (m σ x) = m k 0 := by rw [map_zero]; exact h
        exact hbij.1 this
      · intro h; rw [h, map_zero]
    rw [(hinfl σ k hk).2, hk2]

/-- `a_σ = |ker m_σ|^{-1/4}` (`= (deg μ_σ)^{-1/4}`, N5 L645). -/
noncomputable def normA {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A)) (σ : GQ) :
    ℝ := (Nat.card (m σ).ker : ℝ) ^ (-(1 / 4 : ℝ))

/-- **B1's normalization, proved** (N5 L645-663): from the conjugacy isogenies, `ε = sgn c` is a
normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, and `(m, a = |ker m|^{-1/4},
ε)` is a descent datum. -/
theorem descentDatum_of_conjugacy (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (c : GQ → GQ → ℚ)
    (h : ConjugacyData L A m c) : DescentDatum L A (fun σ τ => sgnU (c σ τ)) := by
  obtain ⟨hgal, hinfl, hend, hfin, hc, hcoc, hcinf, hc11, hdeg, halg⟩ := h
  have hkerL := card_ker_GL hgal hinfl
  have hcard : ∀ σ, 0 < Nat.card (m σ).ker := fun σ => by
    haveI : Finite (m σ).ker := (hfin σ).2.to_subtype
    exact Nat.card_pos
  -- the sign cocycle
  have hloc : IsLocallyConstant (Function.uncurry fun σ τ => sgnU (c σ τ)) := by
    refine isLocallyConstant_of_openSubgroup ((GQL L).prod (GQL L))
      (by rw [Subgroup.coe_prod]; exact L.fixingSubgroup_isOpen.prod L.fixingSubgroup_isOpen)
      _ ?_
    rintro ⟨σ, τ⟩ ⟨k₁, k₂⟩ hk
    rw [Subgroup.mem_prod] at hk
    simp only [Function.uncurry_apply_pair, Prod.mk_mul_mk]
    congr 1
    refine (hcinf σ (σ * k₁) τ (τ * k₂) ?_ ?_).symm
    · intro x hx
      show act σ x = act σ (act k₁ x)
      rw [mem_GQL.mp hk.1 x hx]
    · intro x hx
      show act τ x = act τ (act k₂ x)
      rw [mem_GQL.mp hk.2 x hx]
  refine ⟨⟨hloc, fun σ τ => sgnU_sq _, fun σ τ ρ => ?_⟩, ?_, ?_, m, normA m, ?_, ?_, hgal, hinfl,
    hend, hfin, ?_, halg⟩
  · rw [← sgnU_mul (hc _ _).1 (hc _ _).1, ← sgnU_mul (hc _ _).1 (hc _ _).1, hcoc]
  · exact fun σ σ' τ τ' h1 h2 => by simp only [hcinf σ σ' τ τ' h1 h2]
  · show sgnU (c 1 1) = 1
    rw [hc11]; unfold sgnU; simp
  · intro σ; unfold normA; exact Real.rpow_pos_of_pos (by exact_mod_cast hcard σ) _
  · intro σ k hk
    obtain ⟨h1, h2, h3⟩ := hkerL σ k hk
    unfold normA
    rw [h1, h2, h3]
    simp
  · intro σ τ
    obtain ⟨hc0, n, d, hd, hcnd, hnd⟩ := hc σ τ
    have hn : n ≠ 0 := by
      rintro rfl; apply hc0; rw [hcnd]; simp
    refine ⟨n, d, hn, hd, hnd, ?_⟩
    have hx : (0 : ℝ) < Nat.card (m σ).ker := by exact_mod_cast hcard σ
    have hy : (0 : ℝ) < Nat.card (m τ).ker := by exact_mod_cast hcard τ
    have hz : (0 : ℝ) < Nat.card (m (σ * τ)).ker := by exact_mod_cast hcard (σ * τ)
    have hdegR : (Nat.card (m σ).ker : ℝ) * Nat.card (m τ).ker =
        |(c σ τ : ℝ)| ^ 4 * Nat.card (m (σ * τ)).ker := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hdeg σ τ)
      push_cast at this
      rw [this, pow_abs, abs_of_nonneg (by positivity)]
    have hcR : ((n : ℝ) / d) = (c σ τ : ℝ) := by rw [hcnd]; push_cast; rfl
    have habs : (0 : ℝ) < |(c σ τ : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    have key : normA m σ * normA m τ * |(c σ τ : ℝ)| = normA m (σ * τ) := by
      unfold normA
      rw [← Real.mul_rpow hx.le hy.le, hdegR, Real.mul_rpow (by positivity) hz.le]
      rw [show |(c σ τ : ℝ)| ^ 4 = |(c σ τ : ℝ)| ^ ((4 : ℕ) : ℝ) by norm_cast,
        ← Real.rpow_mul habs.le]
      rw [show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [hcR]
    have e1 : ((normA m σ * normA m τ * (c σ τ : ℝ) : ℝ) : ℂ) =
        ((sgnU (c σ τ) : ℂˣ) : ℂ) * ((normA m σ * normA m τ * |(c σ τ : ℝ)| : ℝ) : ℂ) := by
      have h := sgnU_mul_abs (c σ τ)
      push_cast at h ⊢
      linear_combination (-((normA m σ : ℂ) * (normA m τ : ℂ))) * h
    rw [e1, key]

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

theorem mem_GQL_bot (σ : GQ) : σ ∈ GQL (⊥ : IF) := by
  rw [mem_GQL]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact (act σ).commutes r

theorem galAct_mul {L : IF} (A : PkgI3.AbVar L) (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar) :
    A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
  show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **Sanity check (proved).** For every abelian variety `A` over `ℚ` (here `L = ⊥ ⊆ ℚ̄`), the
Galois action itself is a descent datum with `ε = 1`, `a = 1`, `F_σ = id`. So `DescentDatum` is
not contradictory. -/
theorem descentDatum_bot (A : PkgI3.AbVar (⊥ : IF)) : DescentDatum ⊥ A (fun _ _ => 1) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  refine ⟨⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ => rfl, rfl, m, fun _ => 1, fun _ => one_pos, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul, one_smul, hmul], by simp⟩
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **G4's output (N5 L532-563 and the B1 normalization L632-663).** A finite Galois `L ⊆ ℚ̄`
(the Hom field) with `[L:ℚ] ≤ D`, unramified outside `T`, a QM model `A/L` of `P` (`IsQMModel`), and
the descent datum `ε` of `A` (`DescentDatum`). -/
def G4Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Module.finrank ℚ L ≤ heightD ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
    ∃ (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ), IsQMModel L A P ∧ DescentDatum L A ε

/-- **G7's output (B2-B3, N5 L664-716).** The data of G4 (`L`, `A/L`, `ε`), and: a Dirichlet
character `χ` mod `N`, a locally constant cochain `β : G_ℚ → ℂ^×` with `β² = χ` and `∂β = ε`, and
the kernel field `L' ⊇ L` of `β|_{G_L}`: finite Galois, `G_{L'} = G_L ∩ ker β`,
`[L':ℚ] ≤ Q_D · M_{S_mul}(u)`, and the base change `A_{L'}` is a model of `P`'s surface. -/
def G7Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ),
    IsQMModel L A P ∧ DescentDatum L A ε ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
    (∀ x y, β x * β y = ε x y * β (x * y)) ∧
    (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
    (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-! ## Transitivity of base change -/

/-- `(A_{L'})_{ℚ̄} ≅ A_{ℚ̄}` for `L ≤ L' ⊆ ℚ̄` (pasting of pullbacks). -/
noncomputable def baseChangeTrans {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) :
    ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)).baseChange Qbar).X ≅
      (A.baseChange Qbar).X := by
  letI := incAlg h
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp]
    congr 1
  exact ((Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)))
      (Spec.map (CommRingCat.ofHom (algebraMap L L')))).app A.X).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hcomp)

theorem isModelOver_baseChange {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (hA : IsModelOver L A P) :
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)) P := by
  obtain ⟨e⟩ := hA
  exact ⟨baseChangeTrans h A ≪≫ e⟩

theorem IsQMModel.isModelOver {L : IF} {A : PkgI3.AbVar L} {P : QML3 Qbar}
    (h : IsQMModel L A P) : IsModelOver L A P := by
  obtain ⟨K, hKL, PK, hPK, rfl⟩ := h
  exact isModelOver_baseChange hKL PK.A P hPK

/-! ## G7 from G4 (proved) -/

/-- `max S_mul ≤ D` (copied from `ZInQKernel/Main.lean`, `ZInQ.Mult.le_heightD_of_mem_S_mul`). -/
theorem le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

theorem admissible_S_mul :
    (∀ p ∈ Mult.S_mul, p.Prime) ∧ (∀ p ∈ Mult.S_mul, (p : ℝ) ≤ (heightD : ℝ)) ∧
      (10 : ℝ) ^ 12 ≤ (heightD : ℝ) :=
  ⟨fun _ hp => Mult.prime_of_mem_S_mul hp,
   fun _ hp => by exact_mod_cast le_heightD_of_mem_S_mul hp,
   by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD⟩

/-- **G7 (B2-B3 on the actual descent datum), proved** from G4's output and glue-descent's four
B2 leaves, by `GlueDescent.B3Q.b3_degree_le_QM` at `S = S_mul`, `R = D`, `η = 1`. -/
theorem g7Out_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_degree_le_QM hHasse hTwo hSq hUnr Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u L hLD
      ε hε hinf h11 hram 1 (fun _ => by simp) (IsLocallyConstant.const 1)
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, isModelOver_baseChange hle A P hA.isModelOver⟩

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-- **B2 over `G_ℚ` with the level of `χ` exposed** (the proof of
`GlueDescent.B2Q.b2_of_leaves`, copied; the only change is the extra output
`N = chiLevel T₋ = ∏_{p ∈ T₋} lev p` with `T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`). -/
theorem b2_of_leaves_level (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∃ Tm ⊆ T, N = chiLevel Tm) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, ⟨Tm, Finset.filter_subset _ _, rfl⟩, hsupp, hord, hβl, hβs, hβe⟩

/-- **B3 from a given B2 cochain** (the proof of `GlueDescent.B3Q.b3_of_leaves`, copied, with
`b2_of_leaves`' output taken as hypotheses so that the twist `η` may depend on it). -/
theorem b3_of_cochain
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₁ : GQ → ℂˣ) (hβl₁ : IsLocallyConstant β₁)
    (hβs₁ : ∀ x, β₁ x ^ 2 = galChar χ x) (hβe₁ : ∀ x y, β₁ x * β₁ y = ε x y * β₁ (x * y))
    (tw : GQ →* ℂˣ) (htw : ∀ x, tw x ^ 2 = 1) (htwl : IsLocallyConstant tw) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ),
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β₁ σ * tw σ = 1) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  let β : GQ → ℂˣ := fun x => β₁ x * tw x
  have hβl : IsLocallyConstant β := hβl₁.mul htwl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ tw htw
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ tw
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨L', hle, hfd, hgal, hGL', ?_⟩
  rw [hL', hL]; exact hidx

theorem two_mem_T (u : ℚ) : 2 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_two (by norm_num))

/-- **The data of G7, clause by clause** (the interface handed to G8-G16). For the fibre `P`
over `J(u)`: the Hom field `L` (finite Galois, unramified outside `T`), the model `A/L` with its
descent datum `ε` (B1), the Dirichlet character `χ` mod `N` (`N = ∏_{p ∈ T₋} lev p` for some
`T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`: `χ` is a product of odd characters mod `p` and mod `4`, N5
L677-683, which bounds the conductor of `β` at every prime, as G15 needs), the
cochain `β` (locally constant, `β² = χ`, `∂β = ε`, twisted so that inertia outside `T` dies), and
the kernel field `L' ⊇ L` of `β|_{G_L}`: `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`,
`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/
def G7Data (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist** (N5 L702-716): the data of `G7Data` exist. -/
def G7OutUnr (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL'

/-- **G7 with the twist, proved** from G4's output and the four B2 leaves: B2
(`b2_of_leaves`), the twist killing inertia outside `T` (`GlueB3Unram.unramified_outside_noLeaf`,
no leaf), B3 (`b3_of_cochain`) and the constants (`degree_le_QM`). -/
theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

theorem g7Out_of_g7OutUnr (u : ℚ) (P : QML3 Qbar) (h : G7OutUnr u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hA, hD, hram, -, -, hβl, hβs,
    hβe, hGL', hdeg, -, hM⟩ := h
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, hM⟩

/-! ## G2's bookkeeping (proved) -/

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK

/-- **G2, proved from the fibre cover**: the splitting field is Galois of degree `≤ 324!`
(`GlueRepo.Numerics.splitting_degree_le`). -/
theorem g2Out_of_cover (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ)
    (P : QML3 Qbar) (h : FibreCoverOut Y Φ u P) : G2Out Y Φ u P := by
  obtain ⟨f, hs, hd, hram, A, hA⟩ := h
  have hsp : f.IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgal : IsGalois ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IsGalois.of_separable_splitting_field hs
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) ≤ heightF0 := by
    rw [(Polynomial.IsSplittingField.algEquiv _ f).toLinearEquiv.finrank_eq]
    exact GlueRepo.Numerics.splitting_degree_le f hs hd
  exact ⟨_, hfd, hgal, hdeg, hram, A, hA⟩

/-! ## G4's bookkeeping (proved) -/

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- **G4's input, the kernel field (N5 L540-563 and B1, L632-663; remaining).** For a field `K`
and model `A/K` as in G2's output: `W₀ = Res_{K/ℚ} A` has endomorphism lattice of rank `r ≤ 16F₀²`;
the image of `G_ℚ` on it is a finite subgroup `G ≤ GL_r(ℤ)` with kernel field `E`
(`[E:ℚ] = |G|`), unramified outside `T` (inertia at `p ∉ T` acts trivially on the Tate module of
`W₀`, which has good reduction there); and the base change `A_L` of `A` to the Hom field
`L = E ⊔ K` carries conjugacy isogenies `μ_σ : ^σA → A` over `L`, `B`-linear after the
Skolem-Noether correction, with rational discrepancy (`ConjugacyData`; B1's normalization to a
sign cocycle is proved, `descentDatum_of_conjugacy`). -/
def KernelFieldOut (u : ℚ) (P : QML3 Qbar) (K : IF) (A : PkgI3.AbVar K) : Prop :=
  ∃ (r : ℕ), r ≤ 16 * heightF0 ^ 2 ∧
  ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IF) (_ : FiniteDimensional ℚ E)
    (_ : IsGalois ℚ E), Module.finrank ℚ E = Nat.card G ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt E p) ∧
    ∃ (m : GQ → (PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) →+
        PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right))))
      (c : GQ → GQ → ℚ),
      ConjugacyData (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) m c

/-- **G4, proved from the kernel field**: `L = E ⊔ K` is finite Galois, unramified outside `T`
(`UnramifiedSup`), `[L:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski,
`GlueRepo.TorsionFree.card_le_three_pow`; `GlueRepo.Numerics.a8_field`), `A_L = (PK.A)_L` is a QM
model of `P` (`IsQMModel`), and B1's normalization gives the descent datum
(`descentDatum_of_conjugacy`). -/
theorem g4Out_of_kernelField (hSup : UnramifiedSup) (u : ℚ) (P : QML3 Qbar) (K : IF)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hK : Module.finrank ℚ K ≤ heightF0)
    (hramK : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) (PK : QML3 K)
    (hPK : IsModelOver K PK.A P) (h : KernelFieldOut u P K PK.A) : G4Out u P := by
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hCD⟩ := h
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  have : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg,
    fun p hp => hSup E K p (hramE p hp) (hramK p hp), _, _,
    ⟨K, le_sup_right, PK, hPK, rfl⟩, descentDatum_of_conjugacy _ _ m c hCD⟩

/-! ## The remaining glue as Props, and the composite -/

/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P

/-- **Remaining (G4 + B1): the kernel field of `Res_{K/ℚ} A` and the descent datum on the Hom
field**, for every field `K` and rational fibre `PK/K` as in G2's output (h-decomposition G4: inputs R2, R3, T6,
R7a, T28; A7 proved, `LeafQM.AV.fibre_conjugates_isomorphic`; B1's algebra proved,
glue-descent `B1Quat`, `Cochain`; uses NoCM (G6) for `End⁰(A_ℚ̄) = B`). -/
def KernelFieldExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK → KernelFieldOut u P K PK.A

/-- **G2 → G4 → G7 (proved)**: from the two remaining glue Props and the four B2 leaves, every
fibre context has G7's output. -/
theorem fieldDescent (hCover : FibreCoverExists) (hKer : KernelFieldExists) (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7Out u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7Out_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **G2 → G4 → G7 with the twist (proved)**: as `fieldDescent`, with `L'` unramified outside `T`
and the clause list `G7Data`. -/
theorem fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnr_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-! ## How G7's output feeds `ModularConstituent` -/

/-- (copied from scratch/g0-split/part_split.lean, `G0Split.CommonConstituent`, verbatim) The
hypotheses of E1: for some prime `ℓ` and field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a
common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- **`ModularConstituent`** (scratch/g0-split/part_split.lean, piece 10), copied with
def-faltings' copy `ZInQ.DefFaltings.AbVar` and the bridge `LeafAdopt.abVarEquiv` (the identity on
the underlying scheme) replaced by the kernel's `PkgI3.AbVar`, which `ZInQKernel/HDecomp/`
already uses for both. -/
def ModularConstituentG : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : PkgI3.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent A (J.baseChange L.K)

/-- **The remaining ranges G8-G16 (the next tasks' target), as one Prop.** For every fibre
context and every G7 data (`G7Data`): a level `1 ≤ M ≤ Q_D·M_{S_mul}(u)²`, a `J₁(M)` over `ℚ`, and a
common constituent of `V_ℓ(A_{L'})` and `V_ℓ(J₁(M)_{L'})` as `G_{L'}`-representations (G8: `ρ_ℓ`
from `β`, `a_σ`, `m_σ`; G9-G12: de Rham, odd, modular; G13-G16: newform, level, Eichler-Shimura). -/
def AfterG7 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- **`ModularConstituent` from this range and the next (proved)**: G2, G4, G7 here
(`fieldDescentUnr`) and the ranges G8-G16 as `AfterG7`. -/
theorem modularConstituent_of_ranges (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ :=
    fieldDescentUnr hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdata
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

/-- **The same, with glue-descent's `LeafHasse`, `LeafLocalTwo` replaced by the bundle's T14-T15**
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; `GlueWP3.leafHasse_of_T14`,
`leafLocalTwo_of_T15`). -/
theorem modularConstituent_of_ranges_T14 (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges hCover hKer hSup (GlueWP3.leafHasse_of_T14 hH hR)
    (GlueWP3.leafLocalTwo_of_T15 hC) hSq hUnr hRest

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

/-- (copied) The restriction map `G_K → G_ℚ` (Mathlib's `Field.absoluteGaloisGroup.map`). -/
noncomputable def resQ (K : Type) [Field K] [NumberField K] :
    Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
noncomputable def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied) g0-mod-galois' input "output of G2": inertia at `p ∉ T` lies in `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- (copied) g0-mod-galois' input "output of G7 at the coefficient prime `ℓ`". -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

end GaloisCopy

/-- **Bridge 1 (Mathlib-level Galois theory; proved below, `resQRange`).** For a finite Galois `L' ⊆ ℚ̄`, the
image of `resQ L' : G_{L'} → G_ℚ` is `G_{L'} = Fix(L')` (true for every embedding of the
algebraic closures because `L'/ℚ` is normal). -/
def ResQRange : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    (@GaloisCopy.resQ L' _ (numberField_of_fd L')).range = L'.fixingSubgroup

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (GaloisCopy.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@GaloisCopy.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (GaloisCopy.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : Qbar ≃ₐ[ℚ] Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x


theorem resQRange : ResQRange := fun L' _ _ => resQ_range L'

/-- **g0-mod-galois' `G2Out` for `K = L'`, proved** from `G7Data` (B3(v): inertia outside `T`
fixes `L'`) and `ResQRange`. -/
theorem galoisG2Out_of_g7Data (hRes : ResQRange) (u : ℚ) (P : QML3 Qbar) (L : IF)
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (h : G7Data u P L A ε N χ β L' hLL') :
    @GaloisCopy.G2Out L' _ (numberField_of_fd L') (T u) := by
  intro p hp hpT v hv σ hσ
  rw [hRes L']
  have hv' : GlueB3Unram.LiesOver v p := hv
  exact h.2.2.2.2.2.2.2.2.2.2.1 p hp hpT v hv' (Subgroup.mem_map_of_mem _ hσ)

/-- **Bridge 2 (remaining; the Tate functor on the descent datum, §3 of the report).** From G7's
data, the rank-4 endomorphism ring and `dim A_{L'} = 2` (G5-G6, A9; `model_dim`), for every `ℓ`:
operators `Tm σ` (`ℚ̄_ℓ ⊗ T_ℓ(m_σ)` transported to `V_ℓ(A_{L'})`), `c = n/d`, `a`, `ε`, `β` mapped
into `ℚ̄_ℓ` by one embedding of the number field they generate, and matrix units of
`End_{L'}(A) ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, satisfying g0-mod-galois' `G7Out`. -/
def TateBridge : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu

end G0ModField

end PartModField

/-! # Part 6 (new, task kernel-field): `KernelFieldExists` from the G4 leaves and two glue Props

Everything above is a verbatim copy (see `assemble.sh`). This part proves
`G0ModField.KernelField.kernelFieldExists_of_pieces`:

  `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
  `RaynaudCriterion`, `TorsionStructure` (the kernel's leaves, used by `QML3.goodReduction`)
  + `ConjMapsOnHomField` (glue: the conjugacy maps `m_σ = μ_σ ∘ σ` on the Hom field, with an
    integral discrepancy) + `TorsionCountPts` (glue: `|A(ℚ̄)[n]| = n⁴` for abelian surfaces over
    subfields of `ℚ̄`)
  ⟹ `KernelFieldExists` (g0-mod-field's statement, unchanged).

* §6.1 `conjugacyData_of_maps`: pure algebra. The rational discrepancy `c`, its cocycle identity,
  inflation, `c(1,1) = 1` and the kernel-size identity `|ker m_σ||ker m_τ| = c⁴|ker m_στ|` all
  follow from the maps, an integral relation `d·m_σ m_τ = n·m_στ`, and `|V[n]| = n⁴`.
* §6.2 `kernelField_core`: `homField_core` with the kernel field `E = ℚ̄^{ker ρ}` and the finite
  group `G = ρ(G_ℚ) ≤ GL_r(ℤ)` exposed (`[E:ℚ] = |G|`).
* §6.3 `kernelField_of_model`: G4 (g4-weilres + inertia-homs + morph-descend) in
  `KernelFieldOut`'s shape: `r ≤ 16F₀²`, `G`, `E` unramified outside `T`, and `G_{E⊔K}` fixes
  every homomorphism between the conjugates of `A`.
* §6.4 the hypotheses of G4 on a rational fibre: `hdim` from `G0Dim.dim_baseChange` (g0-dim,
  proved), `hgood` from `QML3.goodReduction` (leaves NOS, Raynaud, TorsionStructure), `hK` from
  `galUnramifiedOutside_iff`.
* §6.5 the remaining glue Props and the headline.
-/

section Part61

open CategoryTheory AlgebraicGeometry Limits
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-! ## §6.1 The discrepancy: pure algebra -/

section Algebra

variable {V : Type*} [AddCommGroup V]

/-- `V[n]`, the `n`-torsion subgroup. -/
abbrev tors (V : Type*) [AddCommGroup V] (n : ℕ) : AddSubgroup V := (n • AddMonoidHom.id V).ker

/-- `|V[n]| = n⁴` for every `n ≥ 1` (the `ℚ̄`-points of an abelian surface in characteristic 0). -/
def TorsCount (V : Type*) [AddCommGroup V] : Prop :=
  ∀ n : ℕ, 0 < n → Nat.card (tors V n) = n ^ 4

theorem mem_tors {n : ℕ} {x : V} : x ∈ tors V n ↔ n • x = 0 := by
  simp [tors, AddMonoidHom.mem_ker]

theorem zsmul_eq_zero_iff_natAbs {d : ℤ} {y : V} : d • y = 0 ↔ d.natAbs • y = 0 := by
  rcases Int.natAbs_eq d with h | h
  · conv_lhs => rw [h]
    rw [natCast_zsmul]
  · conv_lhs => rw [h]
    rw [neg_smul, neg_eq_zero, natCast_zsmul]

/-- A group with `|V[n]| = n⁴` has no nonzero integer exponent. -/
theorem eq_zero_of_forall_zsmul (hT : TorsCount V) {k : ℤ} (hk : ∀ x : V, k • x = 0) : k = 0 := by
  by_contra hk0
  set N := k.natAbs with hN
  have hNpos : 0 < N := Int.natAbs_pos.mpr hk0
  have h1 : tors V N = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    exact zsmul_eq_zero_iff_natAbs.mp (hk x)
  have h2 : tors V (2 * N) = ⊤ := by
    ext x; simp only [mem_tors, AddSubgroup.mem_top, iff_true]
    have hx : x ∈ tors V N := by rw [h1]; exact AddSubgroup.mem_top x
    rw [mem_tors] at hx
    rw [mul_smul, hx, smul_zero]
  have c1 := hT N hNpos
  have c2 := hT (2 * N) (by omega)
  rw [h1] at c1
  rw [h2, c1] at c2
  have h16 : (2 * N) ^ 4 = 16 * N ^ 4 := by ring
  rw [h16] at c2
  have hN4 : 0 < N ^ 4 := pow_pos hNpos 4
  omega

/-- `f = q·g` rationally: `d·f = n·g` with `q = n/d`. -/
def Rel (f g : V →+ V) (q : ℚ) : Prop := ∃ n d : ℤ, d ≠ 0 ∧ q = n / d ∧ d • f = n • g

theorem rel_unique (hT : TorsCount V) {f g : V →+ V} (hg : Function.Surjective g) {q q' : ℚ}
    (h : Rel f g q) (h' : Rel f g q') : q = q' := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  have key : ∀ y : V, (d' * n - d * n') • y = 0 := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    have a := DFunLike.congr_fun e x
    have b := DFunLike.congr_fun e' x
    simp only [AddMonoidHom.smul_apply] at a b
    rw [sub_smul, mul_smul, mul_smul, ← a, ← b, smul_comm d' d, sub_self]
  have := eq_zero_of_forall_zsmul hT key
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hdq' : (d' : ℚ) ≠ 0 := by exact_mod_cast hd'
  rw [div_eq_div_iff hdq hdq']
  have : (d' : ℚ) * n = d * n' := by exact_mod_cast sub_eq_zero.mp this
  linarith

theorem rel_comp_right {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (f.comp k) (g.comp k) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e (k x)
  simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] using a

theorem rel_comp_left {f g : V →+ V} {q : ℚ} (h : Rel f g q) (k : V →+ V) :
    Rel (k.comp f) (k.comp g) q := by
  obtain ⟨n, d, hd, hq, e⟩ := h
  refine ⟨n, d, hd, hq, AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  simp only [AddMonoidHom.smul_apply] at a
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, ← map_zsmul, a]

theorem rel_trans {f g k : V →+ V} {q q' : ℚ} (h : Rel f g q) (h' : Rel g k q') :
    Rel f k (q * q') := by
  obtain ⟨n, d, hd, rfl, e⟩ := h
  obtain ⟨n', d', hd', rfl, e'⟩ := h'
  refine ⟨n * n', d * d', mul_ne_zero hd hd', by push_cast; rw [div_mul_div_comm],
    AddMonoidHom.ext fun x => ?_⟩
  have a := DFunLike.congr_fun e x
  have b := DFunLike.congr_fun e' x
  simp only [AddMonoidHom.smul_apply] at a b ⊢
  rw [mul_comm d d', mul_smul, a, smul_comm, b, ← mul_smul]

theorem rel_self (f : V →+ V) : Rel f f 1 := ⟨1, 1, one_ne_zero, by simp, rfl⟩

/-- `|f⁻¹(H)| = |H|·|ker f|` for surjective `f`. -/
theorem card_comap {f : V →+ V} (hf : Function.Surjective f) (H : AddSubgroup V) :
    Nat.card (H.comap f) = Nat.card H * Nat.card f.ker := by
  let g : H.comap f →+ H := f.addSubgroupComap H
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have e1 : (H.comap f ⧸ g.ker) ≃+ H := QuotientAddGroup.quotientKerEquivOfSurjective g hg
  have e2 : g.ker ≃ f.ker :=
    { toFun := fun x => ⟨x.1.1, AddMonoidHom.mem_ker.mpr
        (congrArg Subtype.val (AddMonoidHom.mem_ker.mp x.2))⟩
      invFun := fun y => ⟨⟨y.1, by
          show f y.1 ∈ H
          rw [AddMonoidHom.mem_ker.mp y.2]; exact H.zero_mem⟩,
        AddMonoidHom.mem_ker.mpr (Subtype.ext (AddMonoidHom.mem_ker.mp y.2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, Nat.card_congr e1.toEquiv,
    Nat.card_congr e2]

theorem card_ker_comp {f g : V →+ V} (hg : Function.Surjective g) :
    Nat.card (f.comp g).ker = Nat.card f.ker * Nat.card g.ker := by
  have : (f.comp g).ker = f.ker.comap g := by
    ext x; simp [AddMonoidHom.mem_ker]
  rw [this, card_comap hg]

theorem card_ker_zsmul (hT : TorsCount V) {f : V →+ V} (hf : Function.Surjective f) {d : ℤ}
    (hd : d ≠ 0) : Nat.card (d • f).ker = d.natAbs ^ 4 * Nat.card f.ker := by
  have : (d • f).ker = (tors V d.natAbs).comap f := by
    ext x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.smul_apply, AddSubgroup.mem_comap, mem_tors]
    exact zsmul_eq_zero_iff_natAbs
  rw [this, card_comap hf, hT _ (Int.natAbs_pos.mpr hd)]

/-- **The kernel identity from the integral relation** (`deg(d·φ) = d⁴ deg φ` on a surface). -/
theorem card_identity (hT : TorsCount V) {f g h : V →+ V} (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hh : Function.Surjective h) {n d : ℤ} (hn : n ≠ 0) (hd : d ≠ 0)
    (e : d • f.comp g = n • h) :
    (Nat.card f.ker : ℚ) * Nat.card g.ker = ((n : ℚ) / d) ^ 4 * Nat.card h.ker := by
  have h1 : Nat.card (d • f.comp g).ker = d.natAbs ^ 4 * Nat.card (f.comp g).ker :=
    card_ker_zsmul hT (f := f.comp g) (hf.comp hg) hd
  have h2 := card_ker_zsmul hT hh hn
  rw [card_ker_comp hg, e] at h1
  rw [h1] at h2
  have hq : ((d.natAbs : ℚ)) ^ 4 = (d : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have hq' : ((n.natAbs : ℚ)) ^ 4 = (n : ℚ) ^ 4 := by
    rw [Nat.cast_natAbs, Int.cast_abs, Even.pow_abs ⟨2, rfl⟩]
  have h3 : ((d.natAbs ^ 4 * (Nat.card f.ker * Nat.card g.ker) : ℕ) : ℚ) =
      ((n.natAbs ^ 4 * Nat.card h.ker : ℕ) : ℚ) := by rw [h2]
  push_cast at h3
  rw [hq, hq'] at h3
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [div_pow]
  field_simp
  linarith

end Algebra

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem act_mul (σ τ : GQ) (x : Qbar) : act (σ * τ) x = act σ (act τ x) := rfl

theorem act_inv_act (σ : GQ) (x : Qbar) : act σ⁻¹ (act σ x) = x := by
  rw [← act_mul, inv_mul_cancel]; rfl

/-- **§6.1, the reduction of `ConjugacyData` to the maps (proved).** For `L` finite Galois and
`A/L` with `|A(ℚ̄)[n]| = n⁴`: maps `m_σ` on `A(ℚ̄)` with `ConjugacyData`'s clauses on the Galois
action, inflation, commutation with `End_L(A)`, surjectivity/finite kernel and algebraicity, and
an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`), carry a rational discrepancy `c` with all of
`ConjugacyData`: `c = n/d` is well defined (`rel_unique`), `≠ 0`, a 2-cocycle, inflated from
`Gal(L/ℚ)`, `c(1,1) = 1`, and `|ker m_σ||ker m_τ| = c⁴|ker m_στ|`. -/
theorem conjugacyData_of_maps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (hend : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ))
    (hfin : ∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite)
    (hdisc : ∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ))
    (halg : ∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ) :
    ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  choose n d hd hnd using hdisc
  let c : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have hsurj : ∀ σ, Function.Surjective (m σ) := fun σ => (hfin σ).1
  have hR : ∀ σ τ, Rel ((m σ).comp (m τ)) (m (σ * τ)) (c σ τ) :=
    fun σ τ => ⟨n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩
  have hn : ∀ σ τ, n σ τ ≠ 0 := by
    intro σ τ hn0
    have key : ∀ y : PtQ L A, d σ τ • y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := ((hsurj σ).comp (hsurj τ)) y
      simp only [Function.comp_apply]
      have a := DFunLike.congr_fun (hnd σ τ) x
      rw [hn0] at a
      simpa only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply, zero_smul] using a
    exact hd σ τ (eq_zero_of_forall_zsmul hT key)
  have hnorm : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hone : (1 : GQ) ∈ GQL L := (GQL L).one_mem
  refine ⟨c, hgal, hinfl, hend, hfin, fun σ τ => ⟨div_ne_zero (by exact_mod_cast hn σ τ)
    (by exact_mod_cast hd σ τ), n σ τ, d σ τ, hd σ τ, rfl, hnd σ τ⟩, ?_, ?_, ?_, ?_, halg⟩
  · -- the cocycle identity
    intro σ τ ρ
    have r1 := rel_trans (rel_comp_right (hR σ τ) (m ρ)) (hR (σ * τ) ρ)
    have r2 := rel_trans (rel_comp_left (hR τ ρ) (m σ)) (hR σ (τ * ρ))
    rw [← _root_.mul_assoc] at r2
    have := rel_unique hT (hsurj _) r1 r2
    rw [mul_comm]; exact this
  · -- inflation from `Gal(L/ℚ)`
    intro σ σ' τ τ' h1 h2
    set k := σ⁻¹ * σ' with hk
    set k' := τ⁻¹ * τ' with hk'
    have hkL : k ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h1 x hx, act_inv_act]
    have hk'L : k' ∈ GQL L := by
      rw [mem_GQL]; intro x hx
      rw [act_mul, ← h2 x hx, act_inv_act]
    have eσ : σ' = σ * k := by rw [hk, mul_inv_cancel_left]
    have eτ : τ' = τ * k' := by rw [hk', mul_inv_cancel_left]
    set k'' := τ⁻¹ * k * τ with hk''
    have hk''L : k'' ∈ GQL L := by
      have := hnorm.conj_mem k hkL τ⁻¹
      rwa [inv_inv] at this
    have hkτ : k * τ = τ * k'' := by rw [hk'']; group
    have hmm : (m σ').comp (m τ') = ((m σ).comp (m τ)).comp (m (k'' * k')) := by
      rw [eσ, eτ, (hinfl σ k hkL).1, (hinfl τ k' hk'L).1, (hinfl k'' k' hk'L).1]
      have h3 : (m k).comp (m τ) = (m τ).comp (m k'') := by
        rw [← (hinfl τ k hkL).2, hkτ, (hinfl τ k'' hk''L).1]
      refine AddMonoidHom.ext fun x => ?_
      have := DFunLike.congr_fun h3 (m k' x)
      simp only [AddMonoidHom.comp_apply] at this ⊢
      rw [this]
    have hgrp : σ' * τ' = σ * τ * (k'' * k') := by
      rw [eσ, eτ, hk'']; group
    have r1 : Rel ((m σ').comp (m τ')) (m (σ' * τ')) (c σ τ) := by
      rw [hmm, hgrp, (hinfl (σ * τ) (k'' * k') ((GQL L).mul_mem hk''L hk'L)).1]
      exact rel_comp_right (hR σ τ) _
    exact (rel_unique hT (hsurj _) (hR σ' τ') r1).symm
  · -- `c(1,1) = 1`
    have r : Rel ((m 1).comp (m 1)) (m (1 * 1)) 1 := by
      rw [← (hinfl 1 1 hone).1]; exact rel_self _
    exact rel_unique hT (hsurj _) (hR 1 1) r
  · -- the kernel identity
    intro σ τ
    exact card_identity hT (hsurj σ) (hsurj τ) (hsurj (σ * τ)) (hn σ τ) (hd σ τ) (hnd σ τ)

/-- **`ConjugacyData` without the discrepancy**: the maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the
Galois action on `G_L`, inflation from `Gal(L/ℚ)`, commutation with `End_L(A)`, surjectivity and
finite kernel, an integral relation `d·m_σ m_τ = n·m_στ` (`d ≠ 0`; Glazer N5 L640-644: the
discrepancy `μ_σ ^σμ_τ μ_στ⁻¹` commutes with `B`, hence is a rational scalar), and algebraicity
(`m_σ(x) = F_σ ∘ x ∘ Spec σ`, `F_σ` finite surjective). Clauses 1-4 and 10 of `ConjugacyData`
verbatim; clause 5 without `c`. -/
def ConjMaps (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ n d : ℤ, d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

theorem conjugacyData_of_conjMaps (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (h : ConjMaps L A m) : ∃ c : GQ → GQ → ℚ, ConjugacyData L A m c := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact conjugacyData_of_maps L A m hT h1 h2 h3 h4 h5 h6

end G0ModField.KernelField

end Part61

/-! ## §6.2-6.3 The kernel field `E` and the group `G ≤ GL_r(ℤ)` (G4, exposed) -/

section KernelCore

open GlueB3Unram GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj

namespace G0ModField.KernelField

/-- **`homField_core` with the kernel field exposed (proved; the proof is `homField_core`'s).**
For a continuous `ℤ`-linear action `ρ` of `G_ℚ` on a free `ℤ`-module with basis `Fin r`, trivial
on inertia outside `T`: `E = ℚ̄^{ker ρ}` is finite Galois with `[E:ℚ] = |G|` for the finite group
`G = ρ(G_ℚ) ≤ GL_r(ℤ)`, `G_E` acts trivially, and `E` is unramified outside `T`. -/
theorem kernelField_core {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M)
    (ρ : Gal →* (M ≃ₗ[ℤ] M)) (hcont : ∀ m : M, IsOpen {σ : Gal | ρ σ m = m})
    (T : Finset ℕ)
    (hinert : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ s ∈ inertiaGQ w, ρ s = 1) :
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧ (∀ σ ∈ E.fixingSubgroup, ρ σ = 1) ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) := by
  classical
  let ρ' : Gal →* Matrix.GeneralLinearGroup (Fin r) ℤ := (G4WeilRes.toGL b).comp ρ
  have hker : ρ'.ker = ρ.ker := by
    ext σ
    simp only [MonoidHom.mem_ker]
    exact G4WeilRes.toGL_eq_one_iff b (ρ σ)
  have hset : (ρ.ker : Set Gal) = ⋂ i, {σ : Gal | ρ σ (b i) = b i} := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_ofPred_eq]
    exact G4WeilRes.eq_one_iff_basis b (ρ σ)
  have hNopen : IsOpen (ρ.ker : Set Gal) := by
    rw [hset]; exact isOpen_iInter_of_finite fun i => hcont (b i)
  have hNclosed : IsClosed (ρ.ker : Set Gal) := Subgroup.isClosed_of_isOpen _ hNopen
  let NC : ClosedSubgroup Gal := { toSubgroup := ρ.ker, isClosed' := hNclosed }
  let E : IntermediateField ℚ Qbar := IntermediateField.fixedField NC.toSubgroup
  have hE : E.fixingSubgroup = ρ.ker := InfiniteGalois.fixingSubgroup_fixedField NC
  have hEfd : FiniteDimensional ℚ E :=
    (InfiniteGalois.isOpen_iff_finite E).mp (by
      show IsOpen (E.fixingSubgroup : Set Gal)
      rw [hE]; exact hNopen)
  have hEgal : IsGalois ℚ E :=
    (InfiniteGalois.normal_iff_isGalois E).mp (by rw [hE]; exact ρ.normal_ker)
  have hcardE : Module.finrank ℚ E = Nat.card ρ'.range := by
    rw [← IsGalois.card_aut_eq_finrank]
    have e1 := QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := ℚ)
      (K₁ := Qbar) E) (AlgEquiv.restrictNormalHom_surjective (E := Qbar))
    have e2 := QuotientGroup.quotientKerEquivRange ρ'
    have c1 : Nat.card (E ≃ₐ[ℚ] E) =
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) E).ker.index :=
      (Nat.card_congr e1.toEquiv).symm
    have c2 : Nat.card ρ'.range = ρ'.ker.index := (Nat.card_congr e2.toEquiv).symm
    rw [c1, c2, IntermediateField.restrictNormalHom_ker, hE, hker]
  haveI : Finite ρ'.range := by
    apply Nat.finite_of_card_ne_zero
    rw [← hcardE]; exact Module.finrank_pos.ne'
  refine ⟨ρ'.range, inferInstance, E, hEfd, hEgal, hcardE, fun σ hσ => ?_, ?_⟩
  · rw [hE] at hσ; exact hσ
  · apply G4WeilRes.unramifiedAt_of_galUnramifiedOutside
    intro p hp hpT w hw s hs
    rw [hE]
    exact hinert p hp hpT w hw s hs

/-- **G4 in `KernelFieldOut`'s shape (proved from the leaves `HomFreeFinite` and
`NeronOggShafarevich`; `MorphismsDescend` is proved, morph-descend).** For `A/K` (`K` finite
Galois, `[K:ℚ] ≤ F₀`, unramified outside `T`) whose conjugates are surfaces and which has good
reduction at every place over every `p ∉ T`: the Hom lattice `⊕ Hom(A_e, A_e')` (the endomorphism
lattice of `Res_{K/ℚ} A ⊗ ℚ̄`) has rank `r ≤ 16F₀²`, the image `G` of `G_ℚ` in `GL_r(ℤ)` is
finite with kernel field `E`, `[E:ℚ] = |G|`, `E` is unramified outside `T`, and `G_{E⊔K}` fixes
every homomorphism between conjugates (`E ⊔ K` is the Hom field). -/
theorem kernelField_of_model (hHFF : HomFreeFinite) (hNOS : PkgI2.NeronOggShafarevich.{0})
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hKF : Module.finrank ℚ K ≤ ZInQ.heightF0) (A : AbVar K)
    (hdim : ∀ e, ((G4WeilRes.conjData K A).A e).dim = 2)
    (T : Finset ℕ) (hK : GalUnramifiedOutside K T)
    (hgood : ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar, PkgI2.HasGoodReduction (ObjBridge.toGrp A) (w.comap (e : K →+* Qbar))) :
    ∃ r : ℕ, r ≤ 16 * ZInQ.heightF0 ^ 2 ∧
    ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IntermediateField ℚ Qbar)
      (_ : FiniteDimensional ℚ E) (_ : IsGalois ℚ E),
      Module.finrank ℚ E = Nat.card G ∧
      (∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt E p) ∧
      (∀ σ ∈ (E ⊔ K).fixingSubgroup, G4WeilRes.conjAction K A σ = 1) := by
  obtain ⟨hfree, hfin, hrank⟩ := G4WeilRes.homLattice_free hHFF (G4WeilRes.conjData K A).A hdim
  have hr : Module.finrank ℤ (G4WeilRes.HomLattice (G4WeilRes.conjData K A).A) ≤
      16 * ZInQ.heightF0 ^ 2 :=
    hrank.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (by rw [G4WeilRes.card_conjugates]; exact hKF) 2))
  obtain ⟨G, hG, E, hfE, hgE, hEG, hfix, hram⟩ :=
    kernelField_core (Module.finBasisOfFinrankEq ℤ _ rfl) (G4WeilRes.conjAction K A)
      (G4WeilRes.conjAction_continuous K G4WeilRes.homDescends A) T
      (G4WeilRes.conjAction_inertia' K (G4WeilRes.inertiaFixesHomsMon_of_leaves hNOS hHFF) A T
        hK hgood)
  exact ⟨_, hr, G, hG, E, hfE, hgE, hEG, hram,
    fun σ hσ => hfix σ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ)⟩

end G0ModField.KernelField

end KernelCore

/-! ## §6.4-6.5 G4's hypotheses on a rational fibre; the remaining Props; the headline -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `hdim` of G4 (proved, from g0-dim's `G0Dim.dim_baseChange`): the conjugates
`A ×_{K,e} ℚ̄` of an abelian surface are surfaces. -/
theorem conj_dim (K : IF) (A : PkgI3.AbVar K) (hA : A.dim = 2) (e : K →ₐ[ℚ] Qbar) :
    ((G4WeilRes.conjData K A).A e).dim = 2 := by
  letI : Algebra K Qbar := (e : K →+* Qbar).toAlgebra
  exact (G0Dim.dim_baseChange (K := K) Qbar A.X.left A.X.hom).trans hA

/-- The base change `A_L` of an abelian surface `A/K` is a surface (g0-dim). -/
theorem bc_dim {K L : IF} (hKL : K ≤ L) (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)).dim = 2 := by
  letI : Algebra K L := incAlg hKL
  exact (G0Dim.dim_baseChange (K := K) L A.X.left A.X.hom).trans hA

/-- `hgood` of G4 on a `QML3` object (G3; proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` through `LeafQM.AV.QML3.goodReduction`, with
inertia-homs' `comap_isDVR` and `isUnit_prime_of_liesOver`): good reduction at every place over
every `p ∉ T` when `3 ∈ T`. -/
theorem good_of_QML3 (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (K : IF) [FiniteDimensional ℚ K] (PK : QML3 K)
    (T : Finset ℕ) (h3 : 3 ∈ T) :
    ∀ p : ℕ, p.Prime → p ∉ T → ∀ w : ValuationSubring Qbar, GlueB3Unram.LiesOver w p →
      ∀ e : K →ₐ[ℚ] Qbar,
        PkgI2.HasGoodReduction (ObjBridge.toGrp PK.A) (w.comap (e : K →+* Qbar)) := by
  intro p hp hpT w hw e
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI := InertiaHoms.comap_isDVR (e : K →+* Qbar) w p hp hw
  have h3u : IsUnit ((3 : ℕ) : w.comap (e : K →+* Qbar)) :=
    InertiaHoms.isUnit_prime_of_liesOver _ w p hp hw 3 Nat.prime_three
      (by rintro rfl; exact hpT h3)
  exact QML3.goodReduction (P := PK) hNOS hRay hTors _ (by simpa using h3u)

/-- **Remaining glue 1 (`|A(ℚ̄)[n]| = n⁴`).** For an abelian surface `A` over a subfield
`L ⊆ ℚ̄`, the `n`-torsion of `A(ℚ̄)` has `n⁴` elements for every `n ≥ 1` (Mumford, *Abelian
varieties*, §4 Application 2 / §6, UNVERIFIED locator: `[n]` is separable of degree `n^{2g}` in
characteristic 0). It is the leaf `PkgI2.TorsionStructure` (`A(K̄)[n] ≅ (ℤ/n)^{2g}` over
`K̄ = AlgebraicClosure K`) transported along `AlgebraicClosure L ≅ ℚ̄` over `L` and from
`PkgI2.Pts (toGrp A)` to `PkgI3.AbVar.Pt`: glue. -/
def TorsionCountPts : Prop :=
  ∀ (L : IF) (A : PkgI3.AbVar L), A.dim = 2 → TorsCount (PtQ L A)

/-- **`TorsionCountPts`, proved from the leaf `PkgI2.TorsionStructure`** (`A(K̄)[n] ≅ (ℤ/n)^{2g}`,
Mumford §4/§6, the kernel's leaf): `ℚ̄` is an algebraic closure of `L` (inertia-homs'
`exists_closure_equiv`), and precomposition with `Spec ι : Spec ℚ̄ ≅ Spec K̄` over `Spec L` is a
bijection of points respecting powers (`MonObj.comp_pow`). -/
theorem torsionCountPts_of_leaf (hTors : PkgI2.TorsionStructure.{0}) : TorsionCountPts := by
  intro L A hA n hn
  obtain ⟨jj, hjj⟩ := InertiaHoms.exists_closure_equiv L L.val
  have hcomp : CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) =
      CommRingCat.ofHom (algebraMap L Qbar) := by
    ext x; exact hjj x
  have hcomp' : CommRingCat.ofHom (algebraMap L Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) =
      CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) := by
    rw [← hcomp]; ext x; simp
  let s : PkgI3.AbVar.ptObj (K := L) Qbar ⟶ PkgI2.specOver L (AlgebraicClosure L) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp])
  let s' : PkgI2.specOver L (AlgebraicClosure L) ⟶ PkgI3.AbVar.ptObj (K := L) Qbar :=
    Over.homMk (Spec.map (CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, hcomp'])
  have h1 : CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) ≫
      CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) = 𝟙 _ := by
    ext x; simp
  have h2 : CommRingCat.ofHom (jj : AlgebraicClosure L →+* Qbar) ≫
      CommRingCat.ofHom (jj.symm : Qbar →+* AlgebraicClosure L) = 𝟙 _ := by
    ext x; simp
  have hss' : s ≫ s' = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h1, Spec.map_id]
  have hs's : s' ≫ s = 𝟙 _ := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, h2, Spec.map_id]
  have hdim : topologicalKrullDim (ObjBridge.toGrp A).X.left = ((2 : ℕ) : WithBot ℕ∞) := by
    change A.dim = _
    rw [hA]; rfl
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨e, -⟩ := hTors L (ObjBridge.toGrp A) 2 n hdim hn (by exact_mod_cast hn.ne')
  let F : PkgI2.torsion (ObjBridge.toGrp A) (AlgebraicClosure L) n ≃ tors (PtQ L A) n :=
    { toFun := fun x => ⟨Additive.ofMul (s ≫ x.1), by
        rw [mem_tors, ← ofMul_pow, ← MonObj.comp_pow]
        have hx : x.1 ^ n = 1 := x.2
        rw [hx, MonObj.comp_one]; rfl⟩
      invFun := fun y => ⟨s' ≫ Additive.toMul y.1, by
        have hy : n • y.1 = 0 := mem_tors.mp y.2
        show (s' ≫ Additive.toMul y.1) ^ n = 1
        rw [← MonObj.comp_pow, ← toMul_nsmul, hy]
        exact MonObj.comp_one _⟩
      left_inv := fun x => by
        apply Subtype.ext
        show s' ≫ s ≫ x.1 = x.1
        rw [← Category.assoc, hs's, Category.id_comp]
      right_inv := fun y => by
        apply Subtype.ext
        show Additive.ofMul (s ≫ s' ≫ Additive.toMul y.1) = y.1
        rw [← Category.assoc, hss', Category.id_comp]; rfl }
  rw [← Nat.card_congr F, Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **Remaining glue 2 (G4 + B1's geometric half on the Hom field: the conjugacy maps).** For
every fibre context, every rational fibre `PK/K` as in G2's output, and every finite Galois
`L ⊇ K` that is a Hom field of `PK.A` (`G_L` fixes every homomorphism between the conjugates of
`PK.A` over `ℚ̄`, g4-weilres' `conjAction`), the base change `A_L` carries the maps
`m_σ = μ_σ ∘ σ` of `ConjMaps` (N5 L632-645: `μ_σ : ^σA → A` the conjugacy isogenies, from A7
`conj_twist_of_rational` and Skolem–Noether, `B`-linear; rational discrepancy by
`End⁰(A_ℚ̄) = B`, i.e. NoCM). -/
def ConjMapsOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **Headline (proved): `KernelFieldExists` from four leaves and two glue Props.** Leaves:
`HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion`, `TorsionStructure` (the kernel's leaves behind `QML3.goodReduction`). Glue:
`TorsionCountPts`, `ConjMapsOnHomField`. Proved on the way: G4 with `E` and `G` exposed
(`kernelField_of_model`), `MorphismsDescend` (morph-descend), `hdim` (g0-dim), `hgood` (G3 on
`QML3` objects), and the discrepancy algebra (`conjugacyData_of_maps`). -/
theorem kernelFieldExists_of_pieces (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hCount : TorsionCountPts)
    (hMaps : ConjMapsOnHomField) : KernelFieldExists := by
  intro Y Φ π u P hctx K _ _ hKF hramK PK hPK
  have hK : GlueB3Unram.GalUnramifiedOutside K (T u) :=
    (G4WeilRes.galUnramifiedOutside_iff K (T u)).mpr hramK
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, hfix⟩ :=
    kernelField_of_model hHFF hNOS K hKF PK.A (conj_dim K PK.A PK.surface) (T u) hK
      (good_of_QML3 hNOS hRay hTors K PK (T u) (three_mem_T u))
  haveI : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  obtain ⟨m, hm⟩ := hMaps Y Φ π u P hctx K hKF hramK PK hPK (E ⊔ K) le_sup_right hfix
  obtain ⟨c, hc⟩ := conjugacyData_of_conjMaps _ _ m
    (hCount _ _ (bc_dim le_sup_right PK.A PK.surface)) hm
  exact ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hc⟩

/-- **Headline, final form (proved): `KernelFieldExists` from four leaves and one glue Prop.**
Leaves: `HomFreeFinite` (Mumford §19 Thm 3), `NeronOggShafarevich` (Serre–Tate 1968 Thm 1),
`RaynaudCriterion` (Raynaud / Grothendieck SGA 7 IX), `TorsionStructure` (Mumford §4/§6).
Glue: `ConjMapsOnHomField` (the conjugacy maps on the Hom field: A7 + Skolem–Noether + NoCM). -/
theorem kernelFieldExists_of_leaves (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hMaps : ConjMapsOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_pieces hHFF hNOS hRay hTors (torsionCountPts_of_leaf hTors) hMaps

end G0ModField.KernelField


/-! ## §6.6 The NoCM input made explicit: `FibreComTrivial` (g0-fibresimple's FS5, verbatim) -/

section FS5Copy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV

namespace G0FibreSimple

/-- **Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). *Why true* (rv-h-cm §7.2, model-checked, no human review): `R1fpProps`,
`R2fpProps` pin down `Y₃` and the Hauptmodul (g0-split §3); the fibre of `X₆ → P¹` over `t(u)` is
a free `W`-orbit with residue field `ℚ(i)` (Elkies' model; `GlueRepo.PR.fibre_free`, proved); a CM
order `R` has conductor prime to 6 with 2, 3 non-split (Vignéras, (Emb)); González–Rotger
Thm 5.12 (leaf R5, `LeafQM.AV.R5ptProps`) and Prop. 5.6 then force `R = ℤ[i]` (excluded since
`t(u) ≠ 1`, `F(u) ≠ 0`) or `#CM(R) = 2 < 4 = #W·x`. Unproved: the Kummer model of `X₆ → P¹`
(function-field Galois theory), the identification of an arbitrary `(Y, Φ, π)` with the bundle's
`X₆`, the class-number arithmetic. Glue, using the leaves R1, R2, R5. -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

end G0FibreSimple

end FS5Copy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Remaining glue 2′ (the conjugacy maps, NoCM given).** As `ConjMapsOnHomField`, with the
NoCM input `End_𝒪(P.A) = ℤ` (FS5's conclusion) as an explicit hypothesis and with only what the
construction uses: moduli data with R1-R2's clauses, a `ℚ̄`-point `y` over a rational `j₀` with
object `P`, a rational fibre `PK/K` over `P`, and a Hom field `L ⊇ K` of `PK.A`. Construction
(N5 L632-645): A7 (`LeafQM.AV.conj_twist_of_rational`, compiled, for every such triple) gives
`^σP ≅ P` up to a twist `α_σ ∈ Aut 𝒪`; Skolem–Noether (T13, proved,
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`) writes `α_σ` as conjugation by `b_σ ∈ B^×`, and
`μ_σ = ι(b_σ)∘(iso)` is a `B`-linear isogeny, defined over the Hom field `L`; the discrepancy
`μ_σ ^σμ_τ μ_στ⁻¹` commutes with `ι(𝒪)`, hence is rational by `End_𝒪 = ℤ`; with T27 (Yu)
`End⁰ = B`, so `m_σ = μ_σ∘σ` commutes with `End_L(A_L)`. The quantifier over `(Y, Φ, π)` costs
nothing here: A7 holds for every triple with R1fp-R2fp, and the NoCM input is a hypothesis. -/
def ConjMapsNoCM : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjMaps L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) m

/-- **`ConjMapsOnHomField` from FS5 and the NoCM-given maps (proved).** -/
theorem conjMapsOnHomField_of (h5 : G0FibreSimple.FibreComTrivial) (h : ConjMapsNoCM) :
    ConjMapsOnHomField := by
  intro Y Φ π u P hctx K _ _ _ _ PK hPK L _ _ hKL hfix
  obtain ⟨hR1, hR2, hu, y, hy, hπ⟩ := hctx
  exact h Y Φ π hR1 hR2 (ZInQ.JHeight.Jmap u) y P hy hπ (h5 Y Φ π hR1 hR2 u hu y P hy hπ) K PK hPK
    L hKL hfix

/-- **Headline with the NoCM input explicit (proved).** `KernelFieldExists` from the leaves
`HomFreeFinite`, `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, the glue FS5
`FibreComTrivial` (g0-fibresimple; its truth for every triple is qm-pin's repair) and the glue
`ConjMapsNoCM`. -/
theorem kernelFieldExists_of_leaves_FS5 (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hMaps : ConjMapsNoCM) : KernelFieldExists :=
  kernelFieldExists_of_leaves hHFF hNOS hRay hTors (conjMapsOnHomField_of h5 hMaps)

end G0ModField.KernelField


/-! ## §6.7 Skolem–Noether on `𝒪` (proved): every twist `α ∈ Aut(𝒪)` is inner in `B`

A7 (`LeafQM.AV.conj_twist_of_rational`) gives `^σP ≅ P` only up to a twist of the QM action by a
ring automorphism `α_σ` of `𝒪`. The algebraic half of the Skolem–Noether descent (N5 L632-640):
`α` extends to a `ℚ`-automorphism of `B = (2,-3)_ℚ` (through the quaternion basis
`α(i), α(j)`), which is inner by Skolem–Noether (T13, proved in
`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`). So `α(a) = u a u⁻¹` for some `u ∈ B^×`, and
`ι(Nu) ∘ (QM iso)` is a `B`-linear isogeny for any `N ≥ 1` with `Nu ∈ 𝒪`. -/

section AutO

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

theorem oj_mul_oi' : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- The quaternion basis `α(i), α(j), α(i)α(j)` of `B` given by a ring automorphism `α` of `𝒪`. -/
noncomputable def autBasis (α : O ≃+* O) : QuaternionAlgebra.Basis B (2 : ℚ) 0 (-3) where
  i := (α oi : B)
  j := (α oj : B)
  k := (α oi : B) * (α oj : B)
  i_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def,
      _root_.mul_one, map_ofNat]
    rfl
  j_mul_j := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oj, map_neg, map_ofNat, Subring.coe_neg,
      Algebra.smul_def, _root_.mul_one, map_neg, map_ofNat]
    rfl
  i_mul_j := rfl
  j_mul_i := by
    rw [← Subring.coe_mul, ← map_mul, oj_mul_oi', map_neg, map_mul]
    simp

/-- **Skolem–Noether on `𝒪` (proved, from T13).** Every ring automorphism `α` of the maximal
order `𝒪 ⊂ B = (2,-3)_ℚ` is conjugation by a unit of `B`. -/
theorem aut_O_inner (α : O ≃+* O) : ∃ u : Bˣ, ∀ a : O, (α a : B) = u * a * (u⁻¹ : Bˣ) := by
  let φ : B →ₐ[ℚ] B := (autBasis α).liftHom
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hbij : Function.Bijective φ :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := φ.toLinearMap)).mp hinj⟩
  obtain ⟨u, hu⟩ := TSkolemKW.leafSkolemNoether ℚ B (AlgEquiv.ofBijective φ hbij)
  refine ⟨u, fun a => ?_⟩
  rw [← hu]
  show (α a : B) = φ a
  let ψ1 : O →+* B := (Subring.subtype O).comp α.toRingHom
  let ψ2 : O →+* B := φ.toRingHom.comp (Subring.subtype O)
  have hi : ψ1 oi = ψ2 oi := by
    show (α oi : B) = (autBasis α).lift (oi : B)
    simp [QuaternionAlgebra.Basis.lift, oi, LeafQM.ofInt, autBasis]
  have hj : ψ1 oj = ψ2 oj := by
    show (α oj : B) = (autBasis α).lift (oj : B)
    simp [QuaternionAlgebra.Basis.lift, oj, LeafQM.ofInt, autBasis]
  obtain ⟨n, hn⟩ := a.2
  have h2 : (2 : O) * a = ((2 * n 0 + n 2 : ℤ) : O) + ((2 * n 1 + n 3 : ℤ) : O) * oi +
      ((n 2 : ℤ) : O) * oj + ((n 3 : ℤ) : O) * (oi * oj) := by
    apply Subtype.ext
    simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
    rw [show ((2 : O) : B) = 2 from rfl, hn]
    ext <;> simp [oi, oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> ring
  have key : ∀ ψ : O →+* B, ψ ((2 : O) * a) = ((2 * n 0 + n 2 : ℤ) : B) +
      ((2 * n 1 + n 3 : ℤ) : B) * ψ oi + ((n 2 : ℤ) : B) * ψ oj +
      ((n 3 : ℤ) : B) * (ψ oi * ψ oj) := by
    intro ψ
    rw [h2]; simp only [map_add, map_mul, map_intCast]
  have e : (2 : B) * ψ1 a = (2 : B) * ψ2 a := by
    have := key ψ1
    rw [map_mul, map_ofNat] at this
    rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
  have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
    rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e
  exact smul_right_injective B (two_ne_zero : (2 : ℚ) ≠ 0) e2

end G0ModField.KernelField

end AutO


/-! ## §6.8 Where NoCM enters (proved): integrality and commutation from `End(A_L) = ι(𝒪)`

`ConjMaps` splits into a geometric part with no NoCM content (`ConjIsogMaps`: the maps
`m_σ = μ_σ∘σ` are `𝒪`-linear, and the discrepancy is an endomorphism of `A_L` up to a nonzero
integer, which holds for any isogenies `μ_σ` by the quasi-inverse `ψ μ_στ = [e]`) and the NoCM
input `End_L(A_L) = ι(𝒪)` (FS5 + T27 + maximality of `𝒪`, on the Hom field). The passage is pure
algebra: an endomorphism commuting with `ι(𝒪)` is `ι(b)` with `b` central in `𝒪`, hence an
integer; faithfulness of `𝒪` on `A(ℚ̄)` follows from `|A[n]| = n⁴` and the anisotropy of the norm
form of `B` (`GlueDescent.aniso_rat`). -/

section NoCMAlg

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-- Every element of `B` has a nonzero integer multiple in `𝒪`. -/
theorem exists_nat_mul_mem_O (y : B) : ∃ N : ℕ, 0 < N ∧ (N : B) * y ∈ O := by
  set D : ℕ := y.re.den * y.imI.den * y.imJ.den * y.imK.den with hD
  have hD0 : 0 < D := by positivity
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * q.den := fun q =>
    (div_eq_iff (by positivity)).mp (Rat.num_div_den q)
  set a : ℤ := y.re.num * (y.imI.den * y.imJ.den * y.imK.den)
  set b : ℤ := y.imI.num * (y.re.den * y.imJ.den * y.imK.den)
  set c : ℤ := y.imJ.num * (y.re.den * y.imI.den * y.imK.den)
  set d : ℤ := y.imK.num * (y.re.den * y.imI.den * y.imJ.den)
  have ha : (a : ℚ) = D * y.re := by simp only [a, hD]; push_cast; rw [hnum]; ring
  have hb : (b : ℚ) = D * y.imI := by simp only [b, hD]; push_cast; rw [hnum]; ring
  have hc : (c : ℚ) = D * y.imJ := by simp only [c, hD]; push_cast; rw [hnum]; ring
  have hd : (d : ℚ) = D * y.imK := by simp only [d, hD]; push_cast; rw [hnum]; ring
  refine ⟨D, hD0, ![a - c, b - d, 2 * c, 2 * d], ?_⟩
  ext <;> simp [LeafQM.ofInt, QuaternionAlgebra.re_natCast, QuaternionAlgebra.imI_natCast,
    QuaternionAlgebra.imJ_natCast, QuaternionAlgebra.imK_natCast] <;> push_cast <;>
    linarith [ha, hb, hc, hd]

/-- A rational element of `𝒪` is an integer. -/
theorem int_of_rat_mem_O {r : ℚ} (h : algebraMap ℚ B r ∈ O) : ∃ k : ℤ, r = k := by
  obtain ⟨n, hn⟩ := h
  have e0 := congrArg QuaternionAlgebra.re hn
  have e1 := congrArg QuaternionAlgebra.imI hn
  have e2 := congrArg QuaternionAlgebra.imJ hn
  have e3 := congrArg QuaternionAlgebra.imK hn
  simp [LeafQM.ofInt, QuaternionAlgebra.algebraMap_eq] at e0 e1 e2 e3
  refine ⟨n 0, ?_⟩
  rw [e0]
  have h2 : (n 2 : ℚ) = 0 := by linarith
  simp [h2]

theorem coe_intCast_O (k : ℤ) : ((k : O) : B) = algebraMap ℚ B k := by
  rw [Subring.coe_intCast, map_intCast]

/-- **The centre of `𝒪` is `ℤ`.** -/
theorem center_O {b : O} (hb : ∀ a : O, b * a = a * b) : ∃ k : ℤ, b = k := by
  have hi : (b : B) * GlueDescent.qi = GlueDescent.qi * b := by
    have := congrArg Subtype.val (hb oi)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oi : O) : B) = GlueDescent.qi by ext <;> simp [oi, LeafQM.ofInt, GlueDescent.qi]]
      at this
  have hj : (b : B) * GlueDescent.qj = GlueDescent.qj * b := by
    have := congrArg Subtype.val (hb oj)
    rw [Subring.coe_mul, Subring.coe_mul] at this
    rwa [show ((oj : O) : B) = GlueDescent.qj by ext <;> simp [oj, LeafQM.ofInt, GlueDescent.qj]]
      at this
  have hs := GlueDescent.B6_commute_i_j (b : B) hi hj
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hs ▸ b.2)
  refine ⟨k, Subtype.ext ?_⟩
  rw [coe_intCast_O, ← hk]
  exact hs

variable {V : Type*} [AddCommGroup V]

/-- **`𝒪` acts faithfully on a group with `|V[n]| = n⁴`.** -/
theorem faithful_O (hT : TorsCount V) (ρ : O →+* AddMonoid.End V) {c : O} (hc : ρ c = 0) :
    c = 0 := by
  by_contra hc0
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O (star (c : B))
  let c' : O := ⟨(N : B) * star (c : B), hmem⟩
  set nf : ℚ := (c : B).re ^ 2 - 2 * (c : B).imI ^ 2 + 3 * (c : B).imJ ^ 2 - 6 * (c : B).imK ^ 2
  have hprod : ((c' * c : O) : B) = algebraMap ℚ B (N * nf) := by
    rw [Subring.coe_mul]
    show (N : B) * star (c : B) * c = _
    rw [_root_.mul_assoc, GlueDescent.B6_star_mul, map_mul, map_natCast]
  obtain ⟨k, hk⟩ := int_of_rat_mem_O (hprod ▸ (c' * c).2)
  have hck : c' * c = (k : O) := Subtype.ext (by rw [hprod, coe_intCast_O, hk])
  have hρ : ρ (k : O) = 0 := by rw [← hck, map_mul, hc, mul_zero]
  rw [map_intCast] at hρ
  have hk0 : k = 0 := eq_zero_of_forall_zsmul hT (fun x => by
    have := DFunLike.congr_fun hρ x
    simpa using this)
  rw [hk0, Int.cast_zero] at hk
  have hnf : nf = 0 := by
    rcases mul_eq_zero.mp hk with h | h
    · exact absurd h (by exact_mod_cast hN.ne')
    · exact h
  obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ hnf
  exact hc0 (Subtype.ext (QuaternionAlgebra.ext h1 h2 h3 h4))


/-- **Skolem–Noether descent at the level of homomorphisms (proved).** A7
(`LeafQM.AV.conj_twist_of_rational`) gives, for each `σ`, a QM isomorphism `e : (A, ι∘α) ≅ (A', ι')`
twisted by some `α ∈ Aut 𝒪`. Writing `α = u(·)u⁻¹` (`aut_O_inner`) and `b = Nu ∈ 𝒪`
(`exists_nat_mul_mem_O`), the homomorphism `μ = e.φ ∘ ι(b) : A → A'` is nonzero-scaled and
`𝒪`-linear: `μ ∘ ι(a) = ι'(a) ∘ μ` for all `a ∈ 𝒪`. This is N5's `B`-linear conjugacy isogeny
`μ_σ` (here `A = P.A`, `A' = (^σP).A`; reverse the roles for `^σA → A`). -/
theorem blinear_of_twisted_iso {k : Type} [Field k] {A A' : PkgI3.AbVar k} (q : QMStr A)
    (q' : QMStr A') (α : O ≃+* O) (e : QMIso (q.twist α) q') :
    ∃ b : O, b ≠ 0 ∧ ∀ a : O,
      (q.iota a).hom ≫ ((q.iota b).hom ≫ e.φ.hom) = ((q.iota b).hom ≫ e.φ.hom) ≫ (q'.iota a).hom := by
  obtain ⟨u, hu⟩ := aut_O_inner α
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O (u : B)
  let b : O := ⟨(N : B) * u, hmem⟩
  have hcomm : ∀ a : O, b * a = α a * b := by
    intro a
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hu a]
    show (N : B) * u * a = u * a * (u⁻¹ : Bˣ) * ((N : B) * u)
    have hc : ((u⁻¹ : Bˣ) : B) * ((N : B) * u) = (N : B) := by
      rw [← _root_.mul_assoc, (Nat.cast_commute N _).symm.eq, _root_.mul_assoc, Units.inv_mul,
        _root_.mul_one]
    rw [_root_.mul_assoc (u * a : B), hc, (Nat.cast_commute N ((u : B) * a)).eq.symm,
      _root_.mul_assoc]
  refine ⟨b, fun hb => ?_, fun a => ?_⟩
  · have h0 := congrArg Subtype.val hb
    change (N : B) * u = 0 at h0
    have h1 := congrArg (· * ((u⁻¹ : Bˣ) : B)) h0
    simp only [_root_.mul_assoc, Units.mul_inv, _root_.mul_one, zero_mul] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    omega
  · have e1 : (q.iota a).hom ≫ (q.iota b).hom = (q.iota b).hom ≫ (q.iota (α a)).hom := by
      show (q.iota b * q.iota a).hom = (q.iota (α a) * q.iota b).hom
      rw [← map_mul, ← map_mul, hcomm]
    rw [← Category.assoc, e1, Category.assoc, Category.assoc]
    congr 1
    exact e.equivariant a

end G0ModField.KernelField

end NoCMAlg


section NoCMSplit

open LeafQM LeafQM.AV

namespace G0ModField.KernelField

/-! Base change on endomorphisms, `End_K(A) → End_L(A_L)` (copied from
`scratch/bp-qmmoduli/QMAbVar.lean` §BaseChangeEnd, lines 528-556, with `AbVar` qualified). -/

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (first half of node N8): `End_K(A) → End_L(A_L)`,
`f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism (functoriality, and
`Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl


/-- The geometric clauses of the conjugacy maps for a ring map `ι' : 𝒪 → End_L(A)` (the QM action
on `A`), with no NoCM content: `ConjMaps`' clauses 1, 2, 4, 6 verbatim; `m_σ` is `𝒪`-linear
(`μ_σ` is `B`-linear, A7 + Skolem–Noether `aut_O_inner`); and the discrepancy is an endomorphism up
to a nonzero integer, `e·m_σ m_τ = δ∘m_στ` with `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ` with `ψ` a
quasi-inverse, `ψ μ_στ = [e]`, Mumford §8; defined over `L` because `L` is a Hom field). -/
def ConjIsogMapsAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (a : O), (m σ).comp (endPt A Qbar (ι' a)) = (endPt A Qbar (ι' a)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      e • (m σ).comp (m τ) = (endPt A Qbar δ).comp (m (σ * τ))) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- **NoCM enters only through `End_L(A) = ι(𝒪)` (proved).** With `|A(ℚ̄)[n]| = n⁴`: the geometric
clauses and `End_L(A) = ι'(𝒪)` give `ConjMaps` (commutation with `End_L(A)`; the discrepancy
`δ = ι'(b)` commutes with `ι'(𝒪)` on points, so `b` is central by faithfulness, hence an
integer). -/
theorem conjMaps_of_qm (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (m : GQ → (PtQ L A →+ PtQ L A)) (hT : TorsCount (PtQ L A))
    (hEnd : ∀ f : PkgI3.AbVar.End A, ∃ a : O, f = ι' a)
    (h : ConjIsogMapsAt L A ι' m) : ConjMaps L A m := by
  obtain ⟨hgal, hinfl, hB, hfin, hdisc, halg⟩ := h
  let ρ : O →+* AddMonoid.End (PtQ L A) := (endPt A Qbar).comp ι'
  have hBx : ∀ σ a x, m σ (ρ a x) = ρ a (m σ x) := fun σ a x =>
    DFunLike.congr_fun (hB σ a) x
  refine ⟨hgal, hinfl, fun σ f => ?_, hfin, fun σ τ => ?_, halg⟩
  · obtain ⟨a, rfl⟩ := hEnd f
    exact hB σ a
  · obtain ⟨e, he, δ, hδ⟩ := hdisc σ τ
    obtain ⟨b, rfl⟩ := hEnd δ
    have hδx : ∀ x, e • m σ (m τ x) = ρ b (m (σ * τ) x) := fun x => by
      have := DFunLike.congr_fun hδ x
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.comp_apply] at this
      exact this
    have hcomm : ∀ a : O, b * a = a * b := by
      intro a
      have h2 : ρ (b * a) = ρ (a * b) := by
        refine AddMonoidHom.ext fun y => ?_
        obtain ⟨x, rfl⟩ := (hfin (σ * τ)).1 y
        rw [map_mul, map_mul]
        show ρ b (ρ a (m (σ * τ) x)) = ρ a (ρ b (m (σ * τ) x))
        rw [← hBx, ← hδx, ← hδx, hBx, hBx, map_zsmul]
      have : ρ (b * a - a * b) = 0 := by rw [map_sub, h2, sub_self]
      exact sub_eq_zero.mp (faithful_O hT ρ this)
    obtain ⟨k, rfl⟩ := center_O hcomm
    refine ⟨k, e, he, ?_⟩
    rw [hδ]
    refine AddMonoidHom.ext fun x => ?_
    have hk : ρ (k : O) = (k : AddMonoid.End (PtQ L A)) := map_intCast ρ k
    show ρ (k : O) (m (σ * τ) x) = _
    rw [hk, AddMonoid.End.intCast_apply, AddMonoidHom.smul_apply]

end G0ModField.KernelField

end NoCMSplit

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField


/-! ### Sanity check (proved): the new clause lists are satisfiable

For an abelian variety over `ℚ` (`L = ⊥`) with any ring map `ι' : 𝒪 → End(A)`, the Galois action
`m_σ = σ` satisfies `ConjIsogMapsAt` (with `e = 1`, `δ = 1`, `F_σ = id`), hence `ConjMaps`. So
the definitions are not contradictory (as g0-mod-field's `descentDatum_bot` for `DescentDatum`). -/

theorem conjIsogMapsAt_bot (A : PkgI3.AbVar (⊥ : IF)) (ι' : LeafQM.O →+* PkgI3.AbVar.End A) :
    ConjIsogMapsAt ⊥ A ι' (fun σ => MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  have hcomm : ∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ) := by
    intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  refine ⟨?_, ?_, fun σ a => hcomm σ (ι' a), ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, one_ne_zero, 1, ?_⟩
    rw [one_smul, hmul, map_one]
    rfl
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **Remaining glue 3 (geometric: the conjugacy maps without NoCM).** For moduli data with
R1-R2's clauses, a `ℚ̄`-point over a rational `j₀` with object `P`, a rational fibre `PK/K` over
`P` and a Hom field `L ⊇ K` of `PK.A`: maps `m_σ = μ_σ∘σ` on `A_L(ℚ̄)` with `ConjIsogMapsAt` for
the base-changed QM action `ι_L = endBC ∘ PK.q.iota`. Inputs (N5 L632-645): A7
(`conj_twist_of_rational`, compiled, every triple), Skolem–Noether on `𝒪` (`aut_O_inner`,
proved), a quasi-inverse of an isogeny (Mumford §8, UNVERIFIED locator), Galois descent of
`G_L`-fixed morphisms to `L`, and the semilinear identification of `^σA` with `A` as schemes. -/
def ConjIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ m : GQ → (PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) →+
            PtQ L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))),
          ConjIsogMapsAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) m

/-- **Remaining glue 4 (NoCM on the Hom field: `End_L(A_L) = ι_L(𝒪)`).** Given FS5's conclusion
`End_𝒪(P.A) = ℤ`: by Yu's dichotomy (T27, leaf) `End⁰(P.A) ≅ B`, so `End(P.A)` is an order of
`ι(B)` containing the maximal order `ι(𝒪)`, hence equal to it; `P ≅ (PK)_ℚ̄` as QM objects (R1's
naturality and `RationalFibre`), and `End_L(A_L) → End_ℚ̄` is injective (faithful base change). -/
def EndEqOOnHomField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- **`ConjMapsNoCM` from the geometric maps and `End_L(A_L) = ι(𝒪)` (proved; leaf
`TorsionStructure` for `|A(ℚ̄)[n]| = n⁴`).** -/
theorem conjMapsNoCM_of (hTors : PkgI2.TorsionStructure.{0}) (hG : ConjIsogMaps)
    (hE : EndEqOOnHomField) : ConjMapsNoCM := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨m, hm⟩ := hG Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact ⟨m, conjMaps_of_qm L _ _ m
    (torsionCountPts_of_leaf hTors L _ (bc_dim hKL PK.A PK.surface))
    (hE Y Φ π hR1 hR2 j₀ y P hy hπ hcom K PK hPK L hKL hfix) hm⟩

/-- **Headline, split form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue `FibreComTrivial`
(FS5, g0-fibresimple), `ConjIsogMaps` (geometric) and `EndEqOOnHomField` (NoCM consequence). -/
theorem kernelFieldExists_of_split (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (hE : EndEqOOnHomField) : KernelFieldExists :=
  kernelFieldExists_of_leaves_FS5 hHFF hNOS hRay hTors h5 (conjMapsNoCM_of hTors hG hE)

/-- **Remaining glue 4a (one QM surface over `ℚ̄`): `End_𝒪 = ℤ ⟹ End = ι(𝒪)`.** For an object `P`
(abelian surface over `ℚ̄` with QM by the maximal order `𝒪` of `(2,-3)_ℚ`) whose `𝒪`-centralizer
is `ℤ`, every endomorphism is `ι(a)`. *Argument* (model check): T27 (Yu 2013, leaf
`PkgI3.QMDichotomyYu`) gives `End⁰ ≅ B` or `M₂(ℚ(√d))`; FS4 (`CentralizerOfMatrixEnd0`, proved
from T6 by g0-fibresimple) excludes the second; `B → End⁰` (g0-fibresimple's `qm_embeds_end0`) is
injective (`B` simple) between 4-dimensional spaces, so `End⁰ = ι(B)`; `End` is an order (T6)
of `ι(B)` containing `ι(𝒪)`, which is maximal, so `End = ι(𝒪)`. No moduli data. -/
def EndEqOFibre : Prop :=
  ∀ P : QML3 Qbar, (∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)) →
    ∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a

/-- **Remaining glue 4b (transport to the Hom field).** If `End(P.A) = ι(𝒪)`, then
`End_L(A_L) = ι_L(𝒪)`: `P ≅ (PK)_ℚ̄` as QM objects (R1's naturality applied to
`RationalFibre`), and base change `End_L(A_L) → End_ℚ̄((A_L)_ℚ̄)` is injective and compatible
with `ι` (`endBC`, faithful base change: bp-qmmoduli's `endBC_injective`). -/
def EndTransport : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    (∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
          ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- `EndEqOOnHomField` from 4a and 4b (proved). -/
theorem endEqOOnHomField_of (ha : EndEqOFibre) (hb : EndTransport) : EndEqOOnHomField := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hcom K _ _ PK hPK L _ _ hKL hfix
  exact hb Y Φ π hR1 hR2 j₀ y P hy hπ (ha P hcom) K PK hPK L hKL hfix

/-- **Headline, finest form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`,
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure` and the glue FS5
`FibreComTrivial`, `ConjIsogMaps`, `EndEqOFibre`, `EndTransport`. -/
theorem kernelFieldExists_of_split' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) (ha : EndEqOFibre) (hb : EndTransport) : KernelFieldExists :=
  kernelFieldExists_of_split hHFF hNOS hRay hTors h5 hG (endEqOOnHomField_of ha hb)

end G0ModField.KernelField


/-! ## §6.9 `EndEqOFibre` from T27, T6 and the maximality of `𝒪`

Copied verbatim from `scratch/g0-fibresimple/olean/Tail.lean`: lines 38-117 (`B6_isUnit`,
`division_of_algEquiv`, `qmBasis`, `qm_embeds_end0`), 152-164 (FS4 `CentralizerOfMatrixEnd0`) and
208-282 (FS4 proved from T6, `centralizerOfMatrixEnd0_of_homFree`). -/

section FS4Copy

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV
open scoped Quaternion TensorProduct

namespace G0FibreSimple

/-! ## §1 Proved glue: `B` is a division algebra -/

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩


/-- **Glue piece FS4 (the CM case of Yu's dichotomy has a non-integral `𝒪`-centralizer).** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for an abelian variety with QM by `𝒪`, then the centralizer
`End_𝒪(A) = com q` contains a non-integer. *Why true* (STANDARD linear algebra): the image of
`B` in `M₂(k)`, `k = ℚ(√d)`, spans `M₂(k)` over `k` (`B ⊗ k` is simple of `k`-dimension 4), so
its centralizer is the centre `k`; `n√d` lies in the image of `End(A)` for some `n ≥ 1`, and
commutation and non-integrality pass from `End⁰(A)` to `End(A)` because `End(A)` is torsion-free
(Mumford §19 Thm 3). Glue. -/
def CentralizerOfMatrixEnd0 : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ φ ∈ com q, ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End A)


/-! ## §4′ Proved: `CentralizerOfMatrixEnd0` from the leaf T6 (`PkgI3.HomFreeFinite`) -/

/-- **FS4 is proved from T6** (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3: `Hom(A, B)` is a free
`ℤ`-module; `TextbookLeaves.t6`). Proof: the scalar matrix `√d` is central in `M₂(ℚ(√d))`, so
`c' = e⁻¹(√d)` is central in `End⁰(A)` and is not a rational scalar (`(√d)² = d < 0`); `ℚ ⊗ End(A)`
is the localization of `End(A)` at `ℤ \ {0}`, so `s • c' = 1 ⊗ φ` for some `φ ∈ End(A)`,
`s ≠ 0`; freeness makes `m ↦ 1 ⊗ m` injective, so `φ` commutes with `ι(𝒪)` and is not an
integer. -/
theorem centralizerOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) :
    CentralizerOfMatrixEnd0 := by
  intro k _ _ A q d hd hM
  obtain ⟨e⟩ := hM
  set c' : PkgI3.AbVar.End0 A :=
    e.symm (Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d))) with hc'
  have hcen : ∀ x : PkgI3.AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') (e x)).eq
  have hnq : ∀ t : ℚ, c' ≠ algebraMap ℚ _ t := by
    intro t ht
    have h1 : Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d)) =
        algebraMap ℚ _ t := by
      rw [← AlgEquiv.commutes e t, ← ht, hc', e.apply_symm_apply]
    have h2 : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d) =
        AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C d) t := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, AdjoinRoot.algebraMap_eq]
        using this
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num
    have h3 := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C d)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h3
    rw [h2, ← map_pow, ← map_sub] at h3
    have h4 : t ^ 2 - d = 0 :=
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg) (h3.trans (map_zero _).symm)
    nlinarith [sq_nonneg t]
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  refine ⟨φ, ?_, ?_⟩
  · rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ - φ * q.iota a) = 0 := by
      have e1 : ∀ x y : PkgI3.AbVar.End A,
          (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
        intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (hinj _ key)
  · intro n hn
    apply hnq ((n : ℚ) / (s : ℤ))
    have h1 : algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c' =
        algebraMap ℚ (PkgI3.AbVar.End0 A) (n : ℚ) := by
      rw [map_intCast, map_intCast, ← zsmul_eq_mul, ← hs', hn]
      exact map_intCast (Algebra.TensorProduct.includeRight :
        PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
    have hs1 : ((s : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs0
    calc c' = algebraMap ℚ (PkgI3.AbVar.End0 A) (((s : ℤ) : ℚ)⁻¹) *
          (algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c') := by
          rw [← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hs1, map_one, _root_.one_mul]
      _ = algebraMap ℚ _ ((n : ℚ) / (s : ℤ)) := by
          rw [h1, ← map_mul, div_eq_inv_mul]

end G0FibreSimple

end

end FS4Copy


/-! ## §6.10 `𝒪` is a maximal order (proved)

An element of `B` integral over `ℤ` has integral reduced trace and norm (division by
`X² - tX + n`, Gauss's lemma `IsIntegrallyClosed.eq_map_mul_C_of_dvd`). For `x` in an order
`R ⊇ 𝒪`, the traces `t₁..t₄` of `x·1, x·i, x·(1+j)/2, x·(i+k)/2` and `nrd(x)` are integers;
`24·nrd(x) = 6t₁² - 3t₂² + 2(t₁-2t₃)² - (2t₄-t₂)²`, and the congruences mod 3 and mod 8
(`decide` on `ZMod 3`, `ZMod 8`) put `x` in `𝒪`. (Python check: of the 36 classes of `𝒪^∨/𝒪`,
only `0` has integral norm.) -/

section OMaxSec

open Polynomial


namespace G0ModField.KernelField

/-- The reduced norm form of `B = (2,-3)_ℚ`. -/
def nrdB (x : LeafQM.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

/-- **An element of `B` integral over `ℤ` has integral reduced trace and norm.** -/
theorem int_of_integral {x : LeafQM.B} (hx : IsIntegral ℤ x) :
    (∃ t : ℤ, 2 * x.re = t) ∧ ∃ n : ℤ, nrdB x = n := by
  by_cases hq : x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0
  · -- `x ∈ ℚ`
    obtain ⟨h1, h2, h3⟩ := hq
    have hxr : x = algebraMap ℚ LeafQM.B x.re := by
      ext <;> simp [QuaternionAlgebra.algebraMap_eq, h1, h2, h3]
    have hint : IsIntegral ℤ x.re := by
      rw [hxr] at hx
      exact (isIntegral_algHom_iff ((Algebra.ofId ℚ LeafQM.B).restrictScalars ℤ)
        (algebraMap ℚ LeafQM.B).injective).mp hx
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hk' : x.re = k := by rw [← hk]; rfl
    refine ⟨⟨2 * k, by rw [hk']; push_cast; ring⟩, ⟨k ^ 2, ?_⟩⟩
    simp only [nrdB, hk', h1, h2, h3]; push_cast; ring
  · obtain ⟨p, hpm, hpx⟩ := hx
    set t : ℚ := 2 * x.re
    set n : ℚ := nrdB x
    let q : ℚ[X] := X ^ 2 - C t * X + C n
    have hqm : q.Monic := by
      have : q = X ^ 2 + (-(C t) * X + C n) := by ring
      rw [this]
      refine Monic.add_of_left (monic_X_pow 2) ?_
      refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · calc (-(C t) * X).degree ≤ 1 := by
              rw [← C_neg]; exact degree_C_mul_X_le _
          _ < (X ^ 2 : ℚ[X]).degree := by rw [degree_X_pow]; norm_num
      · calc (C n).degree ≤ 0 := degree_C_le
          _ < (X ^ 2 : ℚ[X]).degree := by rw [degree_X_pow]; norm_num
    have hqx : aeval x q = 0 := by
      simp only [q, map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_X]
      ext <;> simp [sq, QuaternionAlgebra.algebraMap_eq, t, n, nrdB] <;> ring
    have hpx' : aeval x (p.map (algebraMap ℤ ℚ)) = 0 := by
      rw [aeval_map_algebraMap]; exact hpx
    set r := p.map (algebraMap ℤ ℚ) %ₘ q with hr
    have hrx : aeval x r = 0 := by
      have e := modByMonic_add_div (p.map (algebraMap ℤ ℚ)) q
      have := congrArg (aeval x) e
      rw [map_add, map_mul, hqx, zero_mul, add_zero, hpx'] at this
      exact this
    have hq2 : q.natDegree = 2 := by
      simp only [q]; compute_degree!
    have hrdeg : r.degree ≤ 1 := by
      have := natDegree_modByMonic_lt (p.map (algebraMap ℤ ℚ)) hqm
        (fun h => by rw [h, natDegree_one] at hq2; exact absurd hq2 (by norm_num))
      rw [hq2] at this
      exact degree_le_of_natDegree_le (Nat.lt_succ_iff.mp this)
    have hr0 : r = 0 := by
      rw [eq_X_add_C_of_degree_le_one hrdeg] at hrx ⊢
      simp only [map_add, map_mul, aeval_C, aeval_X] at hrx
      have e1 := congrArg QuaternionAlgebra.imI hrx
      have e2 := congrArg QuaternionAlgebra.imJ hrx
      have e3 := congrArg QuaternionAlgebra.imK hrx
      have e0 := congrArg QuaternionAlgebra.re hrx
      simp [QuaternionAlgebra.algebraMap_eq] at e0 e1 e2 e3
      have hc1 : r.coeff 1 = 0 := by
        by_contra hc
        apply hq
        exact ⟨(e1.resolve_left hc), (e2.resolve_left hc), (e3.resolve_left hc)⟩
      rw [hc1] at e0 ⊢
      simp at e0
      simp [e0]
    have hdvd : q ∣ p.map (algebraMap ℤ ℚ) := (modByMonic_eq_zero_iff_dvd hqm).mp hr0
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hpm hdvd
    rw [hqm.leadingCoeff, C_1, _root_.mul_one] at hg
    have c1 := congrArg (fun f : ℚ[X] => f.coeff 1) hg
    have c0 := congrArg (fun f : ℚ[X] => f.coeff 0) hg
    simp [q, coeff_X, coeff_C] at c1 c0
    refine ⟨⟨-g.coeff 1, ?_⟩, ⟨g.coeff 0, ?_⟩⟩
    · push_cast; linarith
    · linarith

end G0ModField.KernelField

namespace G0ModField.KernelField

theorem zmod3_aux : ∀ u v : ZMod 3, 2 * u ^ 2 - v ^ 2 = 0 → u = 0 ∧ v = 0 := by decide

theorem zmod8_aux : ∀ a b c d : ZMod 8,
    6 * a ^ 2 - 3 * b ^ 2 + 2 * (a - 2 * c) ^ 2 - (2 * d - b) ^ 2 = 0 → 4 * b = 0 ∧ 4 * d = 0 := by
  decide


/-- `𝒪` is a maximal order (statement as `OMaximal` in `New.lean`). -/
theorem oMaximal' : ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) →
    R ≤ LeafQM.O := by
  intro R hOR hint x hx
  have hmem : ∀ v : Fin 4 → ℤ, x * LeafQM.ofInt v ∈ R := fun v =>
    R.mul_mem hx (hOR ⟨v, rfl⟩)
  obtain ⟨⟨t1, ht1⟩, ⟨nn, hnn⟩⟩ := int_of_integral (hint x hx)
  obtain ⟨⟨t2, ht2⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 1, 0, 0]))
  obtain ⟨⟨t3, ht3⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 0, 1, 0]))
  obtain ⟨⟨t4, ht4⟩, -⟩ := int_of_integral (hint _ (hmem ![0, 0, 0, 1]))
  simp [LeafQM.ofInt, QuaternionAlgebra.re_mul] at ht2 ht3 ht4
  unfold nrdB at hnn
  set a := x.re
  set b := x.imI
  set c := x.imJ
  set d := x.imK
  -- `a = t1/2`, `b = t2/4`, `c = (t1 - 2 t3)/6`, `d = (2 t4 - t2)/12`
  have hQ : 6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 = 24 * nn := by
    have : ((6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 : ℤ) : ℚ) =
        ((24 * nn : ℤ) : ℚ) := by
      push_cast
      rw [← ht1, ← hnn]
      have e2 : (t2 : ℚ) = 4 * b := by linarith
      have e3 : (t3 : ℚ) = a - 3 * c := by linarith
      have e4 : (t4 : ℚ) = 2 * b + 6 * d := by linarith
      rw [e2, e3, e4]; ring
    exact_mod_cast this
  -- mod 3
  set u := t1 - 2 * t3 with hu
  set v := 2 * t4 - t2 with hv
  have h3dvd : (3 : ℤ) ∣ 2 * u ^ 2 - v ^ 2 :=
    ⟨8 * nn - 2 * t1 ^ 2 + t2 ^ 2, by linear_combination hQ⟩
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr h3dvd
  push_cast at h3
  obtain ⟨hu3, hv3⟩ := zmod3_aux _ _ h3
  obtain ⟨u', hu'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd u 3).mp hu3
  obtain ⟨v', hv'⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd v 3).mp hv3
  -- mod 8
  have h8dvd : (8 : ℤ) ∣ 6 * t1 ^ 2 - 3 * t2 ^ 2 + 2 * (t1 - 2 * t3) ^ 2 - (2 * t4 - t2) ^ 2 :=
    ⟨3 * nn, by rw [hQ]; ring⟩
  have h8 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr h8dvd
  push_cast at h8
  obtain ⟨hb8, hd8⟩ := zmod8_aux _ _ _ _ h8
  have hb2 : (8 : ℤ) ∣ 4 * t2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hb8)
  have hd2 : (8 : ℤ) ∣ 4 * t4 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp (by push_cast; exact hd8)
  obtain ⟨s2, hs2⟩ : ∃ s, t2 = 2 * s := ⟨t2 / 2, by omega⟩
  obtain ⟨s4, hs4⟩ : ∃ s, t4 = 2 * s := ⟨t4 / 2, by omega⟩
  -- the coordinates of `x` in `𝒪`
  have hn2 : 2 * c = u' := by
    have : (u : ℚ) = 3 * u' := by exact_mod_cast hu'
    rw [hu] at this; push_cast at this; linarith
  obtain ⟨w, hw⟩ : ∃ w : ℤ, v' = 2 * w := ⟨v' / 2, by omega⟩
  have hn3 : 2 * d = w := by
    have : (v : ℚ) = 3 * v' := by exact_mod_cast hv'
    rw [hv] at this; push_cast at this
    have : (v' : ℚ) = 2 * w := by exact_mod_cast hw
    linarith
  have hvz : 2 * t4 - t2 = 3 * v' := by rw [← hv, hv']; norm_num
  have hvq : (3 * v' : ℚ) = 4 * s4 - 2 * s2 := by
    have : 3 * v' = 4 * s4 - 2 * s2 := by rw [← hvz, hs2, hs4]; ring
    exact_mod_cast this
  have es4 : (t4 : ℚ) = 2 * s4 := by exact_mod_cast hs4
  refine ⟨![t3 + u', s4 - v', u', w], ?_⟩
  have e2 : (t2 : ℚ) = 4 * b := by linarith
  have e3 : (t3 : ℚ) = a - 3 * c := by linarith
  have e4 : (t4 : ℚ) = 2 * b + 6 * d := by linarith
  have es2 : (t2 : ℚ) = 2 * s2 := by exact_mod_cast hs2
  ext <;> simp [LeafQM.ofInt] <;> linarith

end G0ModField.KernelField

end OMaxSec

section EndEqOSec

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion

namespace G0ModField.KernelField

/-- **Remaining glue 4a′ (pure algebra): `𝒪` is a maximal order of `B = (2,-3)_ℚ`.** A subring of
`B` containing `𝒪` whose elements are integral over `ℤ` is contained in `𝒪`. STANDARD (the
order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` has reduced discriminant `6 = disc B`; Vignéras,
*Arithmétique des algèbres de quaternions*, III §5, UNVERIFIED locator). A finite lattice
computation, proved below (`oMaximal`). -/
def OMaximal : Prop :=
  ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) → R ≤ LeafQM.O

/-- **`OMaximal`, proved** (§6.10). -/
theorem oMaximal : OMaximal := oMaximal'

/-- **`EndEqOFibre` from T27 (Yu), T6 (Mumford §19 Thm 3) and `OMaximal` (proved).** -/
theorem endEqOFibre_of (t27 : PkgI3.QMDichotomyYu) (hHF : PkgI3.HomFreeFinite)
    (hmax : OMaximal) : EndEqOFibre := by
  intro P hcom f
  have hY := PkgI3.qmDichotomy_B6 t27 Qbar P.A P.surface G0FibreSimple.B6_isUnit
    (G0FibreSimple.qm_embeds_end0 P.q)
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ :=
        G0FibreSimple.centralizerOfMatrixEnd0_of_homFree hHF Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := hcom φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  let φ : LeafQM.B →ₐ[ℚ] PkgI3.AbVar.End0 P.A := (G0FibreSimple.qmBasis P.q).liftHom
  haveI : Nontrivial (PkgI3.AbVar.End0 P.A) := e.toEquiv.nontrivial
  have hinj : Function.Injective φ := φ.toRingHom.injective
  haveI : FiniteDimensional ℚ (PkgI3.AbVar.End0 P.A) :=
    LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hrank : Module.finrank ℚ LeafQM.B = Module.finrank ℚ (PkgI3.AbVar.End0 P.A) :=
    e.toLinearEquiv.finrank_eq.symm
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank (f := φ.toLinearMap)).mp hinj
  let j : PkgI3.AbVar.End P.A →ₐ[ℤ] PkgI3.AbVar.End0 P.A := Algebra.TensorProduct.includeRight
  have hfree : Module.Free ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).1
  haveI : Module.Finite ℤ (PkgI3.AbVar.End P.A) := (hHF Qbar P.A P.A).2.1
  let tm := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End P.A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) tm :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ tm).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End P.A) (S := ℚ))
  have hjinj : Function.Injective j := by
    intro x y hxy
    have hm : (1 : ℚ) ⊗ₜ[ℤ] (x - y) = 0 := by
      rw [TensorProduct.tmul_sub]
      exact sub_eq_zero.mpr hxy
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) tm).mp hm
    rw [Submonoid.smul_def] at hs'
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s'))
  -- `φ` agrees with `j ∘ ι` on `𝒪`
  have hagree : ∀ a : LeafQM.O, φ (a : LeafQM.B) = j (P.q.iota a) := by
    let ψ1 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := φ.toRingHom.comp (Subring.subtype _)
    let ψ2 : LeafQM.O →+* PkgI3.AbVar.End0 P.A := j.toRingHom.comp P.q.iota
    have hi : ψ1 G0FibreSimple.oi = ψ2 G0FibreSimple.oi := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oi : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oi, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    have hj : ψ1 G0FibreSimple.oj = ψ2 G0FibreSimple.oj := by
      show (G0FibreSimple.qmBasis P.q).lift (G0FibreSimple.oj : LeafQM.B) = _
      simp [QuaternionAlgebra.Basis.lift, G0FibreSimple.oj, LeafQM.ofInt, G0FibreSimple.qmBasis]
      rfl
    intro a
    obtain ⟨n, hn⟩ := a.2
    have h2 : (2 : LeafQM.O) * a = ((2 * n 0 + n 2 : ℤ) : LeafQM.O) +
        ((2 * n 1 + n 3 : ℤ) : LeafQM.O) * G0FibreSimple.oi +
        ((n 2 : ℤ) : LeafQM.O) * G0FibreSimple.oj +
        ((n 3 : ℤ) : LeafQM.O) * (G0FibreSimple.oi * G0FibreSimple.oj) := by
      apply Subtype.ext
      simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_intCast]
      rw [show ((2 : LeafQM.O) : LeafQM.B) = 2 from rfl, hn]
      ext <;> simp [G0FibreSimple.oi, G0FibreSimple.oj, LeafQM.ofInt, QuaternionAlgebra.re_ofNat,
        QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;>
        ring
    have key : ∀ ψ : LeafQM.O →+* PkgI3.AbVar.End0 P.A, ψ ((2 : LeafQM.O) * a) =
        ((2 * n 0 + n 2 : ℤ) : PkgI3.AbVar.End0 P.A) +
        ((2 * n 1 + n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oi +
        ((n 2 : ℤ) : PkgI3.AbVar.End0 P.A) * ψ G0FibreSimple.oj +
        ((n 3 : ℤ) : PkgI3.AbVar.End0 P.A) * (ψ G0FibreSimple.oi * ψ G0FibreSimple.oj) := by
      intro ψ
      rw [h2]; simp only [map_add, map_mul, map_intCast]
    have e1 : (2 : PkgI3.AbVar.End0 P.A) * ψ1 a = (2 : PkgI3.AbVar.End0 P.A) * ψ2 a := by
      have := key ψ1
      rw [map_mul, map_ofNat] at this
      rw [this, hi, hj, ← key ψ2, map_mul, map_ofNat]
    have e2 : (2 : ℚ) • ψ1 a = (2 : ℚ) • ψ2 a := by
      rw [two_smul, two_smul, ← two_mul, ← two_mul]; exact e1
    exact smul_right_injective (PkgI3.AbVar.End0 P.A) (two_ne_zero : (2 : ℚ) ≠ 0) e2
  -- the order `R = φ⁻¹(End)`
  let R : Subring LeafQM.B := (j.toRingHom.range).comap φ.toRingHom
  have hOR : LeafQM.O ≤ R := fun x hx => ⟨P.q.iota ⟨x, hx⟩, (hagree ⟨x, hx⟩).symm⟩
  have hint : ∀ x ∈ R, IsIntegral ℤ x := by
    rintro x ⟨g, hg⟩
    have h1 : IsIntegral ℤ g := Algebra.IsIntegral.isIntegral g
    have h2 : IsIntegral ℤ (φ x) := by
      have := h1.map j
      rwa [show j g = φ x from hg] at this
    exact (isIntegral_algHom_iff (φ.restrictScalars ℤ) hinj).mp h2
  obtain ⟨x, hx⟩ := hsurj (j f)
  have hxO : x ∈ LeafQM.O := hmax R hOR hint ⟨f, hx.symm⟩
  refine ⟨⟨x, hxO⟩, hjinj ?_⟩
  rw [← hagree, ← hx]

/-- **Headline, with the NoCM side down to leaves + FS5 + `OMaximal` (proved).** Leaves:
`HomFreeFinite` (T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`,
`QMDichotomyYu` (T27). Glue: FS5 `FibreComTrivial`, `OMaximal` (pure algebra),
`EndTransport`, `ConjIsogMaps`. -/
theorem kernelFieldExists_of_split'' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hmax : OMaximal) (hb : EndTransport)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_split' hHFF hNOS hRay hTors h5 hG (endEqOFibre_of t27 hHFF hmax) hb

/-- **Headline, final split form (proved).** `KernelFieldExists` from the leaves `HomFreeFinite`
(T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, `QMDichotomyYu` (T27) and the
glue FS5 `FibreComTrivial`, `EndTransport`, `ConjIsogMaps`. -/
theorem kernelFieldExists_of_final (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hb : EndTransport) (hG : ConjIsogMaps) :
    KernelFieldExists :=
  kernelFieldExists_of_split'' hHFF hNOS hRay hTors t27 h5 oMaximal hb hG


/-- `End = ι(𝒪)` moves along an isomorphism of `QML3` objects (proved). -/
theorem endEqO_of_iso {k : Type} [Field k] {P Q : QML3 k} (e : QML3.Iso Q P)
    (h : ∀ f : PkgI3.AbVar.End P.A, ∃ a : LeafQM.O, f = P.q.iota a) :
    ∀ g : PkgI3.AbVar.End Q.A, ∃ a : LeafQM.O, g = Q.q.iota a := by
  intro g
  let g' : PkgI3.AbVar.End P.A := PkgI3.AbVar.Hom.mk' (e.ψ.hom ≫ g.hom ≫ e.φ.hom)
  obtain ⟨a, ha⟩ := h g'
  refine ⟨a, PkgI3.AbVar.Hom.ext' ?_⟩
  have h1 : g.hom = e.φ.hom ≫ g'.hom ≫ e.ψ.hom := by
    change g.hom = e.φ.hom ≫ (e.ψ.hom ≫ g.hom ≫ e.φ.hom) ≫ e.ψ.hom
    simp only [Category.assoc, e.left, Category.comp_id]
    rw [← Category.assoc, e.left, Category.id_comp]
  rw [h1, ha, ← Category.assoc, ← e.equivariant a, Category.assoc, e.left, Category.comp_id]

/-- **Remaining glue 4b′ (base change and rigidity).** For a base change `Q` of `PK` along
`K ⊆ ℚ̄` (`IsBaseChangeOf`, a pullback square compatible with `ι` and `η`): if
`End(Q.A) = ι_Q(𝒪)`, then `End_L(A_L) = ι_L(𝒪)` for every `L ⊇ K`. *Argument* (model check):
`(A_L)_ℚ̄` and `Q.A` are two pullbacks of `PK.A` along `Spec ℚ̄ → Spec K` (pasting), hence
isomorphic as `ℚ̄`-schemes; the isomorphism preserves the identity (`η(0) = 0`), so it is a
homomorphism by rigidity (g0-fibresimple's leaf `RigidityHom`, Mumford §4 Cor. 1), and it carries
the base change of `ι_L(a)` to `ι_Q(a)`; an `f ∈ End_L(A_L)` has base change `ι_Q(a)` for some
`a`, so `f = ι_L(a)` because base change along `Spec ℚ̄ → Spec L` is faithful (fpqc;
bp-qmmoduli's `endBC_injective`). `IsBaseChangeOf` records no group law, which is why rigidity
is needed. -/
def EndTransportBC : Prop :=
  ∀ (K : IF) (PK : QML3 K) (Q : QML3 Qbar), IsBaseChangeOf (K.val : K →+* Qbar) PK Q →
    (∀ g : PkgI3.AbVar.End Q.A, ∃ a : LeafQM.O, g = Q.q.iota a) →
    ∀ (L : IF) (hKL : K ≤ L),
      ∀ f : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)),
        ∃ a : LeafQM.O, f = ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) a

/-- `EndTransport` from `EndTransportBC` (proved: R1's naturality at `K ⊆ ℚ̄` gives the base
change `Q` of `PK` with `[Q] = [P]`, so `Q ≅ P`, and `endEqO_of_iso`). -/
theorem endTransport_of (h : EndTransportBC) : EndTransport := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ hEndP K _ _ PK hPK L _ _ hKL hfix f
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 K Qbar K.val yK PK hyK
  have hQP : M3.mk Q = M3.mk P := hQ.symm.trans hyKP
  obtain ⟨e⟩ := Quotient.exact hQP
  exact h K PK Q hbc (endEqO_of_iso e hEndP) L hKL f

/-- **Headline, final form with `EndTransportBC` (proved).** -/
theorem kernelFieldExists_of_final' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hbc : EndTransportBC) (hG : ConjIsogMaps) :
    KernelFieldExists :=
  kernelFieldExists_of_final hHFF hNOS hRay hTors t27 h5 (endTransport_of hbc) hG

end G0ModField.KernelField

end EndEqOSec


/-! ## §6.11 `EndTransportBC` from rigidity (attempt)

Copied verbatim: `RigidityHom` (g0-fibresimple `Tail.lean` lines 357-363) and the faithful base
change instances and `endBC_injective` (bp-qmmoduli `QMAbVar.lean` lines 558-575, `AbVar`
qualified). -/

section RigCopy

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace G0FibreSimple


/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

end G0FibreSimple

namespace G0ModField.KernelField

variable {K : Type} [Field K]

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end G0ModField.KernelField

end RigCopy

section RigProof

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open LeafQM.AV

namespace G0ModField.KernelField

/-- **`EndTransportBC` from the textbook leaf `RigidityHom` (proved).** -/
theorem endTransportBC_of_rigidity (hR : G0FibreSimple.RigidityHom) : EndTransportBC := by
  intro K PK Q hbc hEndQ L hKL f
  letI : Algebra K L := incAlg hKL
  obtain ⟨g, hpb, hι, hη⟩ := hbc
  let sKL := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let sLQ := Spec.map (CommRingCat.ofHom (algebraMap L Qbar))
  let AL : PkgI3.AbVar L := PK.A.baseChange L
  let ALQ : PkgI3.AbVar Qbar := AL.baseChange Qbar
  have hcomp : sLQ ≫ sKL = Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) := by
    rw [← Spec.map_comp]; congr 1
  have hpb1 : IsPullback (pullback.fst AL.X.hom sLQ) (pullback.snd AL.X.hom sLQ) AL.X.hom sLQ :=
    IsPullback.of_hasPullback _ _
  have hpb2 : IsPullback (pullback.fst PK.A.X.hom sKL) (pullback.snd PK.A.X.hom sKL)
      PK.A.X.hom sKL := IsPullback.of_hasPullback _ _
  have hpb3 : IsPullback (pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL)
      (pullback.snd AL.X.hom sLQ) PK.A.X.hom
      (Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar))) := by
    rw [← hcomp]; exact hpb1.paste_horiz hpb2
  let θ : ALQ.X.left ≅ Q.A.X.left := hpb3.isoIsPullback _ _ hpb
  have hθfst : θ.hom ≫ g =
      (pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL : ALQ.X.left ⟶ PK.A.X.left) :=
    hpb3.isoIsPullback_hom_fst _ _ hpb
  have hθsnd : θ.hom ≫ Q.A.X.hom = (pullback.snd AL.X.hom sLQ : ALQ.X.left ⟶ _) :=
    hpb3.isoIsPullback_hom_snd _ _ hpb
  let h : ALQ.X ⟶ Q.A.X := Over.homMk θ.hom hθsnd
  let hinv : Q.A.X ⟶ ALQ.X := Over.homMk θ.inv ((Iso.inv_comp_eq θ).mpr hθsnd.symm)
  have hhi : h ≫ hinv = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.hom_inv_id
  have hih : hinv ≫ h = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.inv_hom_id
  -- the identity sections correspond
  have hu : ∀ {R : Type} [Field R] {U : Over (Spec (CommRingCat.of R))},
      (toUnit U).left = U.hom := fun {R _ U} => by
    have := Over.w (toUnit U); simpa using this
  have hid : ∀ (R : Type) [Field R], Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ :=
    fun R _ => by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hηQ : η[Q.A.X].left ≫ g =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ η[PK.A.X].left := by
    have := hη 0
    have h0Q : Additive.toMul (Q.e.eta 0) = 1 := by rw [map_zero]; rfl
    have h0P : Additive.toMul (PK.e.eta 0) = 1 := by rw [map_zero]; rfl
    rw [h0Q, h0P] at this
    change (toUnit (PkgI3.AbVar.ptObj (K := Qbar) Qbar) ≫ η[Q.A.X]).left ≫ g =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫
        (toUnit (PkgI3.AbVar.ptObj (K := K) K) ≫ η[PK.A.X]).left at this
    rw [Over.comp_left, Over.comp_left, hu, hu] at this
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, hid, Category.assoc] at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  have hηW : η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL =
      Spec.map (CommRingCat.ofHom ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar)) ≫ η[PK.A.X].left := by
    have e1 := G4Conj.one_left_fst sLQ AL.X
    have e2 := G4Conj.one_left_fst sKL PK.A.X
    calc η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ ≫ pullback.fst PK.A.X.hom sKL
        = (η[ALQ.X].left ≫ pullback.fst AL.X.hom sLQ) ≫ pullback.fst PK.A.X.hom sKL :=
          (Category.assoc _ _ _).symm
      _ = (sLQ ≫ η[AL.X].left) ≫ pullback.fst PK.A.X.hom sKL := by erw [e1]
      _ = sLQ ≫ (η[AL.X].left ≫ pullback.fst PK.A.X.hom sKL) := Category.assoc _ _ _
      _ = sLQ ≫ (sKL ≫ η[PK.A.X].left) := by erw [e2]
      _ = _ := by rw [← Category.assoc, hcomp]
  have hunit : η[ALQ.X] ≫ h = η[Q.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb.hom_ext
    · show η[ALQ.X].left ≫ θ.hom ≫ g = η[Q.A.X].left ≫ g
      rw [hθfst, hηW, hηQ]
    · rw [Category.assoc, Over.w h, Over.w η[ALQ.X], Over.w η[Q.A.X]]
  have hunit' : η[Q.A.X] ≫ hinv = η[ALQ.X] := by
    rw [← hunit, Category.assoc, hhi, Category.comp_id]
  haveI hmh : IsMonHom h := hR Qbar ALQ Q.A h hunit
  haveI hmi : IsMonHom hinv := hR Qbar Q.A ALQ hinv hunit'
  -- transport `f` to `Q.A`
  let g' : PkgI3.AbVar.End Q.A := PkgI3.AbVar.Hom.mk' (hinv ≫ (endBC AL Qbar f).hom ≫ h)
  obtain ⟨a, ha⟩ := hEndQ g'
  have hf1 : (endBC AL Qbar f).hom = h ≫ (Q.q.iota a).hom ≫ hinv := by
    have : g'.hom = (Q.q.iota a).hom := by rw [ha]
    change hinv ≫ (endBC AL Qbar f).hom ≫ h = _ at this
    rw [← this]
    simp only [← Category.assoc, hhi, Category.id_comp]
    rw [Category.assoc, hhi, Category.comp_id]
  have hf2 : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom ≫ h = h ≫ (Q.q.iota a).hom := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left]
    apply hpb.hom_ext
    · change (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫ θ.hom ≫ g =
        θ.hom ≫ (Q.q.iota a).hom.left ≫ g
      have hm1 : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫
          (pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) =
          (pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (endBC PK.A L (PK.q.iota a)).hom.left :=
        pullback.lift_fst _ _ _
      have hm2 : (endBC PK.A L (PK.q.iota a)).hom.left ≫
          (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left) =
          (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left) ≫ (PK.q.iota a).hom.left :=
        pullback.lift_fst _ _ _
      rw [hι a, hθfst, ← Category.assoc θ.hom g, hθfst]
      have key : (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom.left ≫
          ((pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left)) =
          ((pullback.fst AL.X.hom sLQ : ALQ.X.left ⟶ AL.X.left) ≫
            (pullback.fst PK.A.X.hom sKL : AL.X.left ⟶ PK.A.X.left)) ≫ (PK.q.iota a).hom.left := by
        erw [← Category.assoc, hm1, Category.assoc, hm2, Category.assoc]
        rfl
      exact key
    · rw [Category.assoc, Category.assoc, Over.w h, Over.w (Q.q.iota a).hom, Over.w h]
      exact Over.w ((Over.pullback sLQ).map ((Over.pullback sKL).map (PK.q.iota a).hom))
  have hf3 : (endBC AL Qbar f).hom = (endBC AL Qbar (endBC PK.A L (PK.q.iota a))).hom := by
    rw [hf1, ← Category.assoc, ← hf2, Category.assoc, hhi, Category.comp_id]
  refine ⟨a, endBC_injective AL Qbar (PkgI3.AbVar.Hom.ext' hf3)⟩

/-- **Headline (proved): `KernelFieldExists` from six leaves and two glue Props.** Leaves:
`HomFreeFinite` (T6), `NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`,
`QMDichotomyYu` (T27), `RigidityHom` (Mumford §4 Cor. 1; g0-fibresimple's textbook leaf). Glue:
FS5 `FibreComTrivial` (g0-fibresimple) and `ConjIsogMaps`. -/
theorem kernelFieldExists_of_rigidity (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (hRig : G0FibreSimple.RigidityHom) (h5 : G0FibreSimple.FibreComTrivial)
    (hG : ConjIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_final' hHFF hNOS hRay hTors t27 h5 (endTransportBC_of_rigidity hRig) hG

end G0ModField.KernelField

end RigProof


/-! # Part MR. scratch/mul-rigidity/MulRigidity.lean lines 3-182 and 205-604 (verbatim).
The copy of `RigidityHom` there (lines 189-196) is identical to the one above (New.lean). -/
section PartMulRigidity


/-!
# mul-rigidity: the textbook leaf `RigidityHom` proved from Mathlib

`RigidityHom` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4‴). The proof
follows Mathlib's proof that proper geometrically integral group schemes are commutative
(`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`, Stacks 0BFD),
with the commutator replaced by an arbitrary `c : G ⊗ G ⟶ Z` that is constant on `{e} × G` and on
`G × {e}` (the rigidity lemma, Mumford §4).
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

variable {K : Type u} [Field K]

theorem isClosedImmersion_point (G : Over (Spec (.of K))) (x : 𝟙_ (Over (Spec (.of K))) ⟶ G) :
    IsClosedImmersion x.left :=
  isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom x.left (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity lemma (two-sided form), over an algebraically closed field.** Let `G` be proper
over `K` with `G ×_K G` integral, `Z` separated of finite type, and `c : G × G → Z` with
`c(e, y) = z` and `c(x, e) = z` (as morphisms, for all `T`-points). Then `c` is constant. -/
theorem rigidity_algClosed [IsAlgClosed K]
    (G Z : Over (Spec (.of K))) [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ G) (z : 𝟙_ (Over (Spec (.of K))) ⟶ Z) (c : G ⊗ G ⟶ Z)
    (h1 : ∀ (T : Over (Spec (.of K))) (y : T ⟶ G), lift (toUnit T ≫ e) y ≫ c = toUnit T ≫ z)
    (h2 : ∀ (T : Over (Spec (.of K))) (x : T ⟶ G), lift x (toUnit T ≫ e) ≫ c = toUnit T ≫ z) :
    c = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : IsClosedImmersion e.left := isClosedImmersion_point G e
  have : Nonempty G.left := ⟨e.left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  have : IsSeparated (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst G Z).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (c.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsClosedImmersion ((lift e z).left ≫ (fst G Z).left) := by
    simpa using inferInstanceAs (IsClosedImmersion e.left)
  have : IsClosedImmersion (lift e z).left := .of_comp _ (g := (fst G Z).left)
  let gm : G ⊗ G ⟶ G ⊗ Z := lift (fst _ _) c
  have : IsProper (gm.left ≫ (fst G Z).left) := by simpa [gm]
  have : IsProper gm.left := .of_comp _ (fst G Z).left
  ext1
  have H : gm.left '' ((fst G G).left ⁻¹' {e.left point}) ⊆ {(lift e z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro H
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints H <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift e z).left.isClosedMap _ hpoint).preimage gm.left.continuous).isOpen_compl
      · exact (e.left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨p, hp⟩, hpe⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : p point = c₀ := congr(($hpe).1)
    let pt : 𝟙_ (Over S) ⟶ G ⊗ G := Over.homMk p hp
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (pt ≫ snd G G)
    have : p ≫ pullback.fst G.hom G.hom = e.left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : p = fc.left ≫ (e ▷ G).left := by dsimp; ext <;> simp [fc, pt, S, this]
    have H₂ : fc ≫ e ▷ G ≫ gm = lift e z := by
      have h1' := h1 _ (pt ≫ snd G G)
      rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h1'
      ext1
      · simp [fc, gm, S]
      · simpa [fc, gm, S] using h1'
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, H⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    gm.left (fst G Z).left (e.left point) (by
      dsimp [-Scheme.Hom.comp_base, gm]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset H)
  have H (x : U) : ((pullback.fst G.hom Z.hom) ⁻¹' {x.1} ∩ Set.range ⇑gm.left).Finite := by
    refine ((((gm.left.imageι ≫ (fst G Z).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ gm.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by ext; simp
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst G Z).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact gm.left.isClosedMap.isClosed_range)]
  refine ext_of_apply_eq Z.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let xe : (G ⊗ Z).left := (lift (fst G G) (toUnit _ ≫ z)).left y
    have hgm : lift (fst G G) (toUnit _ ≫ e) ≫ gm = lift (fst G G) (toUnit _ ≫ z) := by
      ext1
      · simp [gm]
      · simpa [gm] using h2 _ (fst G G)
    have : gm.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ gm.left.continuous
        gm.left.isClosedMap ((H ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, gm])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨(lift (fst G G) (toUnit _ ≫ e)).left y, subset_closure ?_, ?_⟩
        · rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, ← Over.comp_left,
            lift_fst]
        · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hgm]
    convert congr((snd G Z).left $this) using 1
    · simp [gm, ← Scheme.Hom.comp_apply]
    · simp only [xe]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
  · simp

/-- **A pointed morphism of proper group schemes is a homomorphism, over an algebraically closed
field** (rigidity, Mumford §4 Cor. 1). Apply `rigidity_algClosed` to
`c = (μ ≫ h) * ((h ⊗ h) ≫ μ)⁻¹`. -/
theorem isMonHom_of_algClosed [IsAlgClosed K]
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom] [IsIntegral (G ⊗ G).left]
    [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  have hone : ∀ (T : Over (Spec (.of K))), (1 : T ⟶ G) ≫ h = 1 := fun T => by
    rw [Hom.one_def, Hom.one_def, Category.assoc, h0]
  have key := rigidity_algClosed G B η[G] η[B] ((μ ≫ h) * ((h ⊗ₘ h) ≫ μ)⁻¹)
    (fun T y => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.one_mul, hone, _root_.one_mul, mul_inv_cancel,
        Hom.one_def])
    (fun T x => by
      rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, lift_map, ← Hom.mul_def,
        ← Hom.mul_def, ← Hom.one_def, _root_.mul_one, hone, _root_.mul_one, mul_inv_cancel,
        Hom.one_def])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact ⟨h0, key⟩

/-- **Rigidity over any field** (Mumford §4 Cor. 1 / Milne Cor. 2.2): base change to `K̄` and
`isMonHom_of_algClosed`; `Over.pullback` along `Spec K̄ → Spec K` is faithful and monoidal. -/
theorem isMonHom_of_geometricallyIntegral
    (G B : Over (Spec (.of K))) [GrpObj G] [GrpObj B] [IsProper G.hom]
    [GeometricallyIntegral G.hom] [IsSeparated B.hom] [LocallyOfFiniteType B.hom]
    (h : G ⟶ B) (h0 : η[G] ≫ h = η[B]) : IsMonHom h := by
  let f := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let F := Over.pullback f
  let G' := F.obj G
  let B' := F.obj B
  have : IsProper G'.hom := by dsimp [G', F]; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G', F]; infer_instance
  have : IsSeparated B'.hom := by dsimp [B', F]; infer_instance
  have : LocallyOfFiniteType B'.hom := by dsimp [B', F]; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj B' := Functor.grpObjObj
  have h0' : η[G'] ≫ F.map h = η[B'] := by
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, ← F.map_comp, h0]
  have := isMonHom_of_algClosed G' B' (F.map h) h0'
  refine ⟨h0, F.map_injective ?_⟩
  have hm := IsMonHom.mul_hom (F.map h)
  rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc]
    at hm
  simp only [← F.map_comp] at hm
  exact (cancel_epi _).mp hm

end MulRigidity
/-! MulRigidity.lean lines 205-604 (verbatim; Mul.lean body: `MulIsogeny` and its reductions).
Lines 184-203 (`RigidityHom` again and `rigidityHom`) are omitted: `RigidityHom` is above and
`rigidityHom` is restated in New.lean. -/

/-!
# mul-rigidity: the textbook leaf `MulIsogeny` reduced to smaller named Props

`MulIsogeny` is copied verbatim from scratch/g0-fibresimple/FibreSimple.lean (§4″). Mathlib
proves "finite and surjective" from local properties of `[n]`:
* proper (`A` proper) and locally quasi-finite give finite (Zariski's main theorem, Mathlib
  `IsFinite.of_isProper_of_locallyQuasiFinite`, Stacks 02LS);
* a locally quasi-finite closed self-map of an irreducible Noetherian scheme is surjective
  (`surjective_of_lqf_self`, generic-point orbit), so `QuasiFiniteEndSurjective` is proved;
* formally unramified + locally of finite type gives locally quasi-finite;
* `[n]` is formally unramified once the unit section of `A[n]` is an open immersion
  (`diagonal_isPullback`: `Δ_f` is a base change of that section).
Chain: `KerUnitOpenOfCotangentSurj` + `CotangentMulN` (glue, unproved) ⇒ `KerUnitOpen` (leaf,
implied by the published `MulEtale`) ⇒ `MulUnramified` ⇒ `MulIsogeny`.
-/

noncomputable section

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- Formally unramified and locally of finite type implies locally quasi-finite (Mathlib's algebra
instance `Algebra.QuasiFinite` from `EssFiniteType` and `FormallyUnramified`, made affine-local). -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h1 : (f.appLE U V e).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance U V e
  have h2 : (f.appLE U V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

variable {K : Type} [Field K]

/-- A `K`-morphism between abelian varieties is proper (source proper, target separated). -/
theorem isProper_left (A B : PkgI3.AbVar K) (f : A.X ⟶ B.X) : IsProper f.left := by
  have : IsProper (f.left ≫ B.X.hom) := by rw [Over.w]; infer_instance
  exact IsProper.of_comp f.left B.X.hom

/-- **Glue.** A locally quasi-finite open `K`-endomorphism of an abelian variety is finite and
surjective. -/
theorem isIsogenyMor_of_lqf_of_isOpenMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X)
    [LocallyQuasiFinite f.left] (ho : IsOpenMap f.left.base) : PkgI3.AbVar.IsIsogenyMor f := by
  have := isProper_left A A f
  refine ⟨IsFinite.of_isProper_of_locallyQuasiFinite f.left, ⟨?_⟩⟩
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have hcl : IsClopen (Set.range f.left.base) :=
    ⟨f.left.isClosedMap.isClosed_range, ho.isOpen_range⟩
  have hne : (Set.range f.left.base).Nonempty :=
    ⟨_, ⟨η[A.X].left (IsLocalRing.closedPoint K), rfl⟩⟩
  exact Set.range_eq_univ.mp (hcl.eq_univ hne)

/-- Under a locally quasi-finite morphism, a strict specialization maps to two distinct points
(the fibres are discrete, Mathlib `Scheme.Hom.isDiscrete_preimage_singleton`). -/
theorem ne_of_specializes_of_lqf {X Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f]
    {x y : X} (hxy : x ⤳ y) (hne : x ≠ y) : f x ≠ f y := by
  intro heq
  have hd := (f.isDiscrete_preimage_singleton (f y)).to_subtype
  let x' : (f.base ⁻¹' {f y} : Set X) := ⟨x, heq⟩
  let y' : (f.base ⁻¹' {f y} : Set X) := ⟨y, rfl⟩
  have h' : x' ⤳ y' := (subtype_specializes_iff x' y').mpr hxy
  exact hne (congrArg Subtype.val h'.eq)

/-- **A locally quasi-finite closed self-map of an irreducible Noetherian scheme is
surjective.** If `f ξ ≠ ξ` for the generic point `ξ`, then `ξ ⤳ f ξ ⤳ f² ξ ⤳ ⋯` are strict
specializations (continuity, and `ne_of_specializes_of_lqf`), so the closures `cl{fᵐ ξ}` form a
strictly decreasing chain of closed sets, contradicting Noetherianity. So `ξ ∈ range f`, which is
closed, hence everything. -/
theorem surjective_of_lqf_self {X : Scheme} [IrreducibleSpace X] [TopologicalSpace.NoetherianSpace X]
    (f : X ⟶ X) [LocallyQuasiFinite f] (hc : IsClosedMap f.base) :
    Function.Surjective f.base := by
  set ξ := genericPoint X
  have hξ : ∀ x : X, ξ ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hfix : f ξ = ξ := by
    by_contra hne
    let s : ℕ → X := fun m => (f.base)^[m] ξ
    have hs : ∀ m, s m ⤳ s (m + 1) ∧ s m ≠ s (m + 1) := by
      intro m
      induction m with
      | zero => exact ⟨hξ _, fun h => hne h.symm⟩
      | succ m ih =>
        have e1 : s (m + 1) = f (s m) := Function.iterate_succ_apply' _ _ _
        have e2 : s (m + 1 + 1) = f (s (m + 1)) := Function.iterate_succ_apply' _ _ _
        rw [e1, e2]
        exact ⟨ih.1.map f.base.hom.continuous, ne_of_specializes_of_lqf f ih.1 ih.2⟩
    let c : ℕ → TopologicalSpace.Closeds X := fun m => ⟨closure {s m}, isClosed_closure⟩
    have hc' : StrictAnti c := by
      refine strictAnti_nat_of_succ_lt fun m => ?_
      refine lt_of_le_of_ne ?_ ?_
      · change closure {s (m + 1)} ⊆ closure {s m}
        exact specializes_iff_closure_subset.mp (hs m).1
      · intro h
        have h2 : closure {s (m + 1)} = closure {s m} := congrArg SetLike.coe h
        exact (hs m).2 (inseparable_iff_closure_eq.mpr h2.symm).eq
    exact not_strictAnti_of_wellFoundedLT c hc'
  intro y
  have hy : y ∈ closure {ξ} := specializes_iff_mem_closure.mp (hξ y)
  exact (hc.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ⟨ξ, hfix⟩)) hy

end MulRigidity

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

end G0FibreSimple

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Leaf (Mumford, *Abelian varieties*, §4 Application 2 and §6: `n_X` is separable when
`char k ∤ n`; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2: `n_A` is étale iff
`char k ∤ n`; locators UNVERIFIED).** In characteristic `0`, `[n]` is étale for `n ≠ 0`. A
consequence of the published statement (only characteristic `0`). -/
def MulEtale : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    Etale ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (the infinitesimal half of `MulEtale`; Mumford §4: `d(n_X) = n` on the tangent space
at `0`, so `n_X^* ω = n ω` for invariant differentials; locator UNVERIFIED).** In characteristic
`0`, `[n]` is formally unramified (`Ω_{[n]} = 0`) for `n ≠ 0`. Implied by `MulEtale`
(`mulUnramified_of_mulEtale`). -/
def MulUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    FormallyUnramified ((n : PkgI3.AbVar.End A).hom).left

/-- **Leaf (dimension theory; Mumford §4 / Milne, *Abelian varieties*, Prop. 8.1: a homomorphism
of abelian varieties of the same dimension with finite kernel is surjective, an isogeny; locators
UNVERIFIED).** A locally quasi-finite endomorphism of an abelian variety is surjective
(any characteristic). -/
def QuasiFiniteEndSurjective : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : PkgI3.AbVar.End A),
    LocallyQuasiFinite f.hom.left → Surjective f.hom.left

theorem mulUnramified_of_mulEtale (h : MulEtale) : MulUnramified := by
  intro k _ _ A n hn
  have := h k A n hn
  infer_instance

/-- **`MulIsogeny` from `MulEtale`** (glue proved here). -/
theorem mulIsogeny_of_mulEtale (h : MulEtale) : G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact isIsogenyMor_of_lqf_of_isOpenMap A _ (Scheme.Hom.isOpenMap _)

/-- **`MulIsogeny` from `MulUnramified` and `QuasiFiniteEndSurjective`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified (h1 : MulUnramified) (h2 : QuasiFiniteEndSurjective) :
    G0FibreSimple.MulIsogeny := by
  intro k _ _ A n hn
  have := h1 k A n hn
  have := isProper_left A A ((n : PkgI3.AbVar.End A).hom)
  have := locallyQuasiFinite_of_formallyUnramified ((n : PkgI3.AbVar.End A).hom).left
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, h2 k A _ inferInstance⟩

/-- **`QuasiFiniteEndSurjective` holds** (proved from Mathlib; it is not a leaf). -/
theorem quasiFiniteEndSurjective : QuasiFiniteEndSurjective := by
  intro k _ A f hf
  have := isProper_left A A f.hom
  have : IrreducibleSpace A.X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := A.X.hom)
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : IsNoetherian A.X.left := { __ := LocallyOfFiniteType.isLocallyNoetherian A.X.hom }
  exact ⟨surjective_of_lqf_self f.hom.left f.hom.left.isClosedMap⟩

/-- **`MulIsogeny` from the single leaf `MulUnramified`** (glue proved here). -/
theorem mulIsogeny_of_mulUnramified' (h : MulUnramified) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified h quasiFiniteEndSurjective

end MulRigidity


/-! ## `MulUnramified` reduced to a statement at the origin of the kernel `A[n]` -/

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The unit section `Spec K → ker f = A ×_{f, A, e} Spec K` of the kernel of a homomorphism. -/
def kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    𝟙_ (Over (Spec (.of K))) ⟶ pullback f η[A.X] :=
  pullback.lift η[A.X] (𝟙 _) (by rw [IsMonHom.one_hom, Category.id_comp])

/-- `(x, y) ↦ x⁻¹ y : A ×_{f, A, f} A → ker f`. -/
def diffKer (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    pullback f f ⟶ pullback f η[A.X] :=
  pullback.lift ((pullback.fst f f)⁻¹ * pullback.snd f f) (toUnit _) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

/-- **The diagonal of a homomorphism `f` is the base change of the unit section of `ker f`**
along `(x, y) ↦ x⁻¹ y` (the square is cartesian: `x⁻¹ y = e ⇔ x = y`). -/
theorem diagonal_isPullback (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsPullback (toUnit A.X) (pullback.diagonal f) (kerUnit A f) (diffKer A f) := by
  have key : ∀ {T : Over (Spec (.of K))} (a : T ⟶ pullback f f),
      a ≫ diffKer A f ≫ pullback.fst f η[A.X] = (a ≫ pullback.fst f f)⁻¹ * (a ≫ pullback.snd f f) := by
    intro T a
    simp only [diffKer, pullback.lift_fst, MonObj.comp_mul, GrpObj.comp_inv]
  refine IsPullback.flip ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst f f)
    ?_ ?_ ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, key, pullback.diagonal_fst, pullback.diagonal_snd, inv_mul_cancel,
        Category.assoc]
      simp only [kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  · intro c
    have hc := congrArg (· ≫ pullback.fst f η[A.X]) c.condition
    simp only [Category.assoc] at hc
    simp only [kerUnit, pullback.lift_fst] at hc
    rw [key, toUnit_unique c.snd (toUnit _), ← Hom.one_def, inv_mul_eq_one] at hc
    apply pullback.hom_ext
    · simp
    · simp [hc]
  · intro c
    exact toUnit_unique _ _
  · intro c m hm _
    rw [← hm, Category.assoc, pullback.diagonal_fst, Category.comp_id]

/-- **Glue.** If the unit section of `ker f` is an open immersion, the homomorphism `f` is formally
unramified (its diagonal is an open immersion, as a base change of the unit section). -/
theorem formallyUnramified_of_kerUnit (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f]
    (h : IsOpenImmersion (kerUnit A f).left) : FormallyUnramified f.left := by
  have hP := (Over.forget _).map_isPullback (diagonal_isPullback A f)
  have h1 : IsOpenImmersion (pullback.diagonal f).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hP h
  let e := PreservesPullback.iso (Over.forget (Spec (.of K))) f f
  have he : pullback.diagonal f.left = (pullback.diagonal f).left ≫ e.hom := by
    apply pullback.hom_ext
    · rw [pullback.diagonal_fst, Category.assoc]
      erw [PreservesPullback.iso_hom_fst]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.fst f f).left
      rw [← Over.comp_left, pullback.diagonal_fst]
      rfl
    · rw [pullback.diagonal_snd, Category.assoc]
      erw [PreservesPullback.iso_hom_snd]
      show 𝟙 _ = (pullback.diagonal f).left ≫ (pullback.snd f f).left
      rw [← Over.comp_left, pullback.diagonal_snd]
      rfl
  have : IsOpenImmersion (pullback.diagonal f.left) := by rw [he]; infer_instance
  infer_instance

/-- **Leaf (Mumford, *Abelian varieties*, §4, Application 2 and §6: `A[n]` is étale, of order
`n^{2g}`, when `char k ∤ n`; equivalently `d[n] = n` on the tangent space at `0`; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Thm 8.2; locators UNVERIFIED).** In characteristic `0`, for
`n ≠ 0`, the unit section of the kernel `A[n] = A ×_{[n], A, e} Spec k` is an open immersion
(`A[n]` is unramified over `k` at the origin: its tangent space there, `ker(n · : Lie A → Lie A)`,
vanishes). A consequence of "`A[n]` is étale over `k`" (a section of an étale separated morphism
is an open immersion; `kerUnitOpen_of_mulEtale`). -/
def KerUnitOpen : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    IsOpenImmersion (kerUnit A ((n : PkgI3.AbVar.End A).hom)).left

/-- A section of a formally unramified morphism locally of finite type is an open immersion
(Stacks 024T; from Mathlib's `isOpenImmersion_diagonal` and
`MorphismProperty.hasOfPostcompProperty_iff_le_diagonal`). -/
theorem isOpenImmersion_of_section {X Y : Scheme} (s : Y ⟶ X) (q : X ⟶ Y)
    [FormallyUnramified q] [LocallyOfFiniteType q] (h : s ≫ q = 𝟙 _) : IsOpenImmersion s := by
  set gr : Y ⟶ pullback (s ≫ q) q := pullback.lift (𝟙 Y) s (by simp)
  have e : s = gr ≫ pullback.snd _ _ := by simp [gr]
  rw [e]
  have h1 : IsOpenImmersion gr :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pullback_lift_diagonal_isPullback s q)
      (FormallyUnramified.isOpenImmersion_diagonal q)
  have h2 : IsOpenImmersion (pullback.snd (s ≫ q) q) :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (by rw [h]; exact (inferInstance : IsOpenImmersion (𝟙 Y)))
  infer_instance

/-- **`KerUnitOpen` is a consequence of `MulEtale`** (so it is implied by the published
statement): the kernel is a base change of `[n]`, hence étale over `k`, and its unit section is a
section of an étale morphism. -/
theorem kerUnitOpen_of_mulEtale (h : MulEtale) : KerUnitOpen := by
  intro k _ _ A n hn
  have hE : Etale ((n : PkgI3.AbVar.End A).hom).left := h k A n hn
  have hP := (Over.forget _).map_isPullback
    (IsPullback.of_hasPullback ((n : PkgI3.AbVar.End A).hom) η[A.X])
  have : Etale (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hP hE
  refine isOpenImmersion_of_section _ (pullback.snd ((n : PkgI3.AbVar.End A).hom) η[A.X]).left ?_
  rw [← Over.comp_left]
  simp [kerUnit]

/-- `MulUnramified` from `KerUnitOpen` (glue proved here). -/
theorem mulUnramified_of_kerUnitOpen (h : KerUnitOpen) : MulUnramified := by
  intro k _ _ A n hn
  exact formallyUnramified_of_kerUnit A _ (h k A n hn)

/-- **`MulIsogeny` from the single leaf `KerUnitOpen`.** -/
theorem mulIsogeny_of_kerUnitOpen (h : KerUnitOpen) : G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_mulUnramified' (mulUnramified_of_kerUnitOpen h)

end MulRigidity


/-! ## `KerUnitOpen` reduced to two glue statements on the cotangent space at the origin -/

namespace MulRigidity

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K]

/-- The origin of `A`, as a point of the underlying space. -/
def origin (A : PkgI3.AbVar K) : A.X.left := η[A.X].left (IsLocalRing.closedPoint K)

theorem map_origin (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    f.left (origin A) = origin A := by
  have h := congrArg (fun g : 𝟙_ (Over (Spec (.of K))) ⟶ A.X => g.left) (IsMonHom.one_hom f)
  simp only [Over.comp_left] at h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g : (𝟙_ (Over (Spec (.of K)))).left ⟶ A.X.left => g (IsLocalRing.closedPoint K)) h)

/-- The local ring `𝒪_{A,0}` at the origin. -/
abbrev O0 (A : PkgI3.AbVar K) : CommRingCat := A.X.left.presheaf.stalk (origin A)

/-- The local endomorphism `f^♯ : 𝒪_{A,0} → 𝒪_{A,0}` of a homomorphism `f` (which fixes `0`). -/
def stalkEndo (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : O0 A ⟶ O0 A :=
  (A.X.left.presheaf.stalkCongr (Inseparable.of_eq (map_origin A f).symm)).hom ≫
    f.left.stalkMap (origin A)

instance (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] : IsLocalHom (stalkEndo A f).hom := by
  unfold stalkEndo
  rw [CommRingCat.hom_comp]
  infer_instance

/-- The cotangent map `m₀/m₀² → m₀/m₀²` of a homomorphism `f` at the origin. -/
def cotangentMap (A : PkgI3.AbVar K) (f : A.X ⟶ A.X) [IsMonHom f] :
    IsLocalRing.CotangentSpace (O0 A) →ₗ[ℤ] IsLocalRing.CotangentSpace (O0 A) :=
  Ideal.mapCotangent _ _ (stalkEndo A f).hom.toIntAlgHom (fun x hx => by
    simp only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (isUnit_of_map_unit (stalkEndo A f).hom x hu))

/-- **Glue (commutative algebra of the fibre `ker f`; Nakayama).** For a homomorphism `f : A → A`
over `k` whose cotangent map at the origin is surjective, the unit section of `ker f` is an open
immersion. *Why true* (STANDARD): `𝒪_{ker f, 0} = 𝒪_{A,0} / f^♯(m₀)𝒪_{A,0}` (the fibre of `f`
over the rational point `0`), so surjectivity gives `m₀ = f^♯(m₀)𝒪 + m₀²`, hence
`m₀ = f^♯(m₀)𝒪` by Nakayama, so `𝒪_{ker f, 0} = k`; a rational point of a Noetherian scheme with
local ring a field is isolated, and the open point is `Spec k`. Glue, unproved. -/
def KerUnitOpenOfCotangentSurj : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (f : A.X ⟶ A.X) [IsMonHom f],
    Function.Surjective (cotangentMap A f) → IsOpenImmersion (kerUnit A f).left

/-- **Glue (the group law to first order; Mumford §4, `d(n_X) = n`, UNVERIFIED locator).** The
cotangent map of `[n]` at the origin is multiplication by `n`, for every `n ∈ ℤ` and in every
characteristic. *Why true* (STANDARD): the unit axioms give `μ^♯(φ) ≡ φ ⊗ 1 + 1 ⊗ φ` modulo
`m ⊗ m` on cotangent spaces, so the cotangent map of `f * g = μ ∘ (f, g)` is the sum of those of
`f` and `g`; induct on `n`. Glue, unproved. -/
def CotangentMulN : Prop :=
  ∀ (k : Type) [Field k] (A : PkgI3.AbVar k) (n : ℤ),
    cotangentMap A ((n : PkgI3.AbVar.End A).hom) = n • LinearMap.id

/-- The residue field at the origin has characteristic `0` when `k` does. -/
theorem charZero_residueField [CharZero K] (A : PkgI3.AbVar K) :
    CharZero (IsLocalRing.ResidueField (O0 A)) := by
  let φ : K →+* IsLocalRing.ResidueField (O0 A) :=
    (IsLocalRing.residue (O0 A)).comp ((A.X.left.presheaf.Γgerm (origin A)).hom.comp
      ((A.X.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom))
  exact (RingHom.charZero_iff φ.injective).mp inferInstance

/-- **`KerUnitOpen` from the two glue statements** (proved here: in characteristic `0`,
multiplication by `n ≠ 0` is bijective on the cotangent space, a vector space over the residue
field). -/
theorem kerUnitOpen_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    KerUnitOpen := by
  intro k _ _ A n hn
  apply h1
  rw [h2]
  have := charZero_residueField A
  have hn' : (n : IsLocalRing.ResidueField (O0 A)) ≠ 0 := Int.cast_ne_zero.mpr hn
  intro v
  refine ⟨((n : IsLocalRing.ResidueField (O0 A))⁻¹) • v, ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply,
    ← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField (O0 A)), smul_smul, mul_inv_cancel₀ hn',
    one_smul]

/-- **`MulIsogeny` from glue alone**: the two cotangent-space glue statements imply it, with no
literature leaf. -/
theorem mulIsogeny_of_cotangent (h1 : KerUnitOpenOfCotangentSurj) (h2 : CotangentMulN) :
    G0FibreSimple.MulIsogeny :=
  mulIsogeny_of_kerUnitOpen (kerUnitOpen_of_cotangent h1 h2)

end MulRigidity
end -- closes the noncomputable section opened at line 222 of the copy
end -- closes the noncomputable section opened at line 15 of the copy
end PartMulRigidity

/-! # Part PTS. scratch/kf-glue/Points.lean (new; the two point lemmas from Mathlib) -/
section PartPoints

/-! # kf-glue: the two point lemmas (prototype; copied into New.lean) -/

noncomputable section

namespace KfGluePoints

open CategoryTheory AlgebraicGeometry Limits

abbrev Qb : Type := AlgebraicClosure ℚ

/-- The ring of a finite affine scheme over `Spec ℚ̄`, and its structure map from `ℚ̄`. -/
def phi (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) :
    CommRingCat.of Qb ⟶ Γ(P, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Qb)).inv ≫ q.appTop

theorem q_eq (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) :
    q = P.isoSpec.hom ≫ Spec.map (phi P q) := by
  have h := Scheme.isoSpec_hom_naturality q
  rw [Scheme.isoSpec_Spec_hom] at h
  rw [phi, Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

theorem phi_finite (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    (phi P q).hom.Finite := by
  rw [phi, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (Scheme.Hom.finite_appTop q)
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

/-- Sections of `q` correspond to ring maps `ψ : Γ(P) → ℚ̄` with `ψ ∘ φ = id`. -/
theorem section_iff (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb))
    (ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb) :
    (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = 𝟙 _ ↔ phi P q ≫ ψ = 𝟙 _ := by
  have hq := q_eq P q
  have e : (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = Spec.map (phi P q ≫ ψ) := by
    conv_lhs => rw [hq]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  rw [e, ← Spec.map_id]
  exact Spec.map_injective.eq_iff

/-- **A nonempty finite scheme over `Spec ℚ̄` has a section.** -/
theorem exists_section (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q]
    [Nonempty P] : ∃ s : Spec (CommRingCat.of Qb) ⟶ P, s ≫ q = 𝟙 _ := by
  have : IsAffine P := isAffine_of_isAffineHom q
  have hB : Nontrivial Γ(P, ⊤) := by
    rw [← PrimeSpectrum.nonempty_iff_nontrivial]
    exact ⟨P.isoSpec.hom (Classical.arbitrary P)⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(P, ⊤)
  let f : Qb →+* (Γ(P, ⊤) ⧸ m) := (Ideal.Quotient.mk m).comp (phi P q).hom
  have hf : f.IsIntegral :=
    (RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
      (phi_finite P q)).to_isIntegral
  have : m.IsMaximal := hm
  have hbij := IsAlgClosed.ringHom_bijective_of_isIntegral f hf
  let e := RingEquiv.ofBijective f hbij
  let ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb :=
    CommRingCat.ofHom ((e.symm : (Γ(P, ⊤) ⧸ m) →+* Qb).comp (Ideal.Quotient.mk m))
  refine ⟨Spec.map ψ ≫ P.isoSpec.inv, (section_iff P q ψ).mpr ?_⟩
  ext r
  change e.symm (f r) = r
  exact e.symm_apply_apply r

/-- **A finite scheme over `Spec ℚ̄` has finitely many sections.** -/
theorem finite_sections (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _}.Finite := by
  have : IsAffine P := isAffine_of_isAffineHom q
  letI : Algebra Qb Γ(P, ⊤) := (phi P q).hom.toAlgebra
  have : Module.Finite Qb Γ(P, ⊤) := phi_finite P q
  have hpre : ∀ s : Spec (CommRingCat.of Qb) ⟶ P, ∃ ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb,
      Spec.map ψ = s ≫ P.isoSpec.hom := fun s => Spec.map_surjective _
  choose ψ hψ using hpre
  have hs : ∀ s, s = Spec.map (ψ s) ≫ P.isoSpec.inv := fun s => by
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let g : {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _} → (Γ(P, ⊤) →ₐ[Qb] Qb) := fun s =>
    { toRingHom := (ψ s.1).hom
      commutes' := fun r => by
        have h1 : phi P q ≫ ψ s.1 = 𝟙 _ := by
          rw [← section_iff P q, ← hs]; exact s.2
        exact congrArg (fun k : CommRingCat.of Qb ⟶ CommRingCat.of Qb => k.hom r) h1 }
  have hg : Function.Injective g := by
    intro s t hst
    apply Subtype.ext
    rw [hs s.1, hs t.1]
    have : ψ s.1 = ψ t.1 := by
      ext x; exact congrArg (fun k : Γ(P, ⊤) →ₐ[Qb] Qb => k x) hst
    rw [this]
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

/-- **`LiftQbarPoints`'s content.** -/
theorem liftQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F) (hs : Surjective F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) : ∃ x : Spec (CommRingCat.of Qb) ⟶ X, x ≫ F = y := by
  have : IsFinite F := hF
  have : Surjective F := hs
  have : Nonempty (Limits.pullback F y : Scheme.{0}) := by
    obtain ⟨p, -⟩ := (pullback.snd F y).surjective (Classical.arbitrary _)
    exact ⟨p⟩
  obtain ⟨s, hs'⟩ := exists_section (pullback F y) (pullback.snd F y)
  refine ⟨s ≫ pullback.fst F y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs', Category.id_comp]

/-- **`FiniteFibreQbarPoints`'s content.** -/
theorem finiteFibreQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) :
    {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y}.Finite := by
  have : IsFinite F := hF
  have := (finite_sections (pullback F y) (pullback.snd F y)).to_subtype
  let ℓ : {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y} →
      {s : Spec (CommRingCat.of Qb) ⟶ pullback F y | s ≫ pullback.snd F y = 𝟙 _} := fun x =>
    ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  have hℓ : Function.Injective ℓ := by
    intro x x' h
    apply Subtype.ext
    have h1 : pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]) =
        pullback.lift x'.1 (𝟙 _) (by rw [x'.2, Category.id_comp]) := congrArg Subtype.val h
    have h2 := congrArg (fun t : Spec (CommRingCat.of Qb) ⟶ pullback F y => t ≫ pullback.fst F y) h1
    simpa using h2
  exact Set.finite_coe_iff.mp (Finite.of_injective ℓ hℓ)

end KfGluePoints
end -- closes Points.lean's noncomputable section
end PartPoints


/-! # kf-glue, part 1: `EndTransport` (scratch/kernel-field/New.lean, statement unchanged)

`EndTransport` is defined above (verbatim from scratch/kernel-field). kernel-field proved
`endTransport_of : EndTransportBC → EndTransport` and
`endTransportBC_of_rigidity : RigidityHom → EndTransportBC`; mul-rigidity proved `RigidityHom`
from Mathlib (`MulRigidity.isMonHom_of_geometricallyIntegral`). -/

section KfGlueEndTransport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`RigidityHom` holds** (mul-rigidity's proof, verbatim apart from the name). -/
theorem G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

/-- **`EndTransport` is a theorem** (no hypotheses). -/
theorem G0ModField.KernelField.endTransport : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- `KernelFieldExists` with `RigidityHom` discharged: five leaves and two glue Props. -/
theorem G0ModField.KernelField.kernelFieldExists_of_five (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hG : G0ModField.KernelField.ConjIsogMaps) :
    G0ModField.KernelFieldExists :=
  G0ModField.KernelField.kernelFieldExists_of_rigidity hHFF hNOS hRay hTors t27
    G0FibreSimple.rigidityHom h5 hG

end KfGlueEndTransport


#print axioms G0ModField.KernelField.endTransport
#print axioms G0ModField.KernelField.kernelFieldExists_of_five

/-! # kf-glue, part 2: `ConjIsogMaps`, level 1 — the points bookkeeping (proved)

`ConjIsogMaps` (verbatim above, from scratch/kernel-field) asks for maps `m_σ` on `A_L(ℚ̄)`. We
prove it from `SemilinearIsogMaps`, the same statement one level down: σ-semilinear finite
surjective scheme endomorphisms `F_σ` of `A_L` (the conjugacy isogenies `μ_σ` composed with the
identification of `^σA_L` and `A_L` as schemes), respecting the group law and the `𝒪`-action,
inflated from `Gal(L/ℚ)`, with discrepancy in `End_L(A_L)` up to an integer; plus two general
glue facts about `ℚ̄`-points of finite morphisms. Then `m_σ(x) = F_σ ∘ x ∘ Spec σ`. -/

section KfGlueLevel1

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Glue (general scheme theory; Stacks, finite morphisms and points over algebraically closed
fields).** A finite surjective morphism of schemes is surjective on `ℚ̄`-points: the fibre over the
image point `y` of `Spec ℚ̄ → Y` is nonempty, and for `x` in it `κ(x)/κ(y)` is algebraic, so the
embedding `κ(y) → ℚ̄` extends to `κ(x)` (`ℚ̄` algebraically closed). -/
def LiftQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F → Surjective F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y, ∃ x : Spec (CommRingCat.of Qbar) ⟶ X, x ≫ F = y

/-- **Glue (general scheme theory).** The `ℚ̄`-points of `X` over a fixed `ℚ̄`-point of `Y` under a
finite morphism form a finite set: the fibre is finite and each `κ(x)/κ(y)` is a finite extension,
which has finitely many `κ(y)`-embeddings into `ℚ̄`. -/
def FiniteFibreQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y,
      {x : Spec (CommRingCat.of Qbar) ⟶ X | x ≫ F = y}.Finite

/-- **The σ-semilinear conjugacy isogenies on `A/L` (geometric clauses).** For each `σ ∈ G_ℚ` a
morphism of schemes `F_σ : A → A` with:
* `F_σ` lies over `Spec(σ⁻¹|_L)` on `Spec L` and respects the group law (it is `μ_σ ∘ c_σ`,
  `c_σ : A ≅ ^σA` the identification of underlying schemes, `μ_σ : ^σA → A` a homomorphism);
* `F_σ` commutes with `ι'(𝒪)` (`μ_σ` is `𝒪`-linear: A7 + Skolem–Noether);
* `F_σ` is finite and surjective (`μ_σ` an isogeny);
* `F_k = id` for `k ∈ G_L` and `F` is constant on double cosets of `G_L` (`μ` inflated from
  `Gal(L/ℚ)`, defined over `L`);
* `F_τ ≫ F_σ ≫ [e] = F_{στ} ≫ δ` with `e ≠ 0` and `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ_{στ}` with
  `ψ_{στ} μ_{στ} = [e]` a quasi-inverse, Mumford §8). -/
def SemilinearIsogAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) : Prop :=
  ∀ σ : GQ,
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ F σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (F σ) (F σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ F σ = F σ ≫ (ι' a).hom.left) ∧
    IsFinite (F σ) ∧ Surjective (F σ) ∧
    (∀ k ∈ GQL L, F k = 𝟙 _ ∧ F (σ * k) = F σ ∧ F (k * σ) = F σ) ∧
    (∀ τ : GQ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      F τ ≫ F σ ≫ (e : PkgI3.AbVar.End A).hom.left = F (σ * τ) ≫ δ.hom.left)

/-- **`ConjIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`; asks for
the σ-semilinear isogenies `F_σ` of `SemilinearIsogAt` on `A_L` for `ι_L = endBC ∘ PK.q.iota`. -/
def SemilinearIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ F : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left),
          SemilinearIsogAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) F

/-- `Spec σ` for `σ ∈ G_ℚ`. -/
noncomputable abbrev specA (σ : GQ) : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar))

theorem specA_mul (σ τ : GQ) : specA (σ * τ) = specA σ ≫ specA τ := by
  rw [specA, specA, specA, ← Spec.map_comp]; rfl

theorem specA_one : specA 1 = 𝟙 _ := by
  rw [specA, ← Spec.map_id]; rfl

theorem specA_inv (σ : GQ) : specA σ ≫ specA σ⁻¹ = 𝟙 _ := by
  rw [← specA_mul, mul_inv_cancel, specA_one]

theorem specA_inv' (σ : GQ) : specA σ⁻¹ ≫ specA σ = 𝟙 _ := by
  rw [← specA_mul, inv_mul_cancel, specA_one]

instance (σ : GQ) : IsIso (specA σ) := ⟨⟨specA σ⁻¹, specA_inv σ, specA_inv' σ⟩⟩

section Pts

variable {L : IF} (A : PkgI3.AbVar L)

/-- The underlying morphism `Spec ℚ̄ → A` of a point. -/
noncomputable def ptl (x : A.Pt Qbar) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := x.left

theorem ptl_w (x : A.Pt Qbar) :
    ptl A x ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := Over.w x

theorem ptl_ext {x y : A.Pt Qbar} (h : ptl A x = ptl A y) : x = y := Over.OverMorphism.ext h

theorem ptl_mul (x y : A.Pt Qbar) :
    ptl A (x * y) = pullback.lift (ptl A x) (ptl A y) ((ptl_w A x).trans (ptl_w A y).symm) ≫
      μ[A.X].left := by
  unfold ptl
  rw [Hom.mul_def, Over.comp_left, Over.lift_left]
  exact rfl

/-- The group-law clause for a semilinear `G` over `Spec τ`. -/
def SemMul (τ : L ≃+* L) (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))) : Prop :=
  μ[A.X].left ≫ G =
    pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left

/-- The image of a point under a σ-semilinear map. -/
noncomputable def semPt (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (x : A.Pt Qbar) : A.Pt Qbar :=
  Over.homMk (specA σ ≫ ptl A x ≫ G) (by
    have hw : (specA σ ≫ ptl A x ≫ G) ≫ A.X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
      rw [Category.assoc, Category.assoc, hG, ← Category.assoc (ptl A x), ptl_w, specA,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext z
      change act σ ((τ z : L) : Qbar) = (z : Qbar)
      rw [hτσ z, ← act_mul, mul_inv_cancel]; rfl
    exact hw)

theorem semPt_ptl (σ : GQ) (τ : L ≃+* L) (hτσ) (G : A.X.left ⟶ A.X.left) (hG)
    (x : A.Pt Qbar) : ptl A (semPt A σ τ hτσ G hG x) = specA σ ≫ ptl A x ≫ G := rfl

theorem semPt_mul (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x y : A.Pt Qbar) :
    semPt A σ τ hτσ G hG (x * y) = semPt A σ τ hτσ G hG x * semPt A σ τ hτσ G hG y := by
  apply ptl_ext
  have hμ' : μ[A.X].left ≫ G = pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left := hμ
  rw [semPt_ptl, ptl_mul, ptl_mul, Category.assoc, hμ', ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [semPt_ptl]
  · simp [semPt_ptl]

/-- `semPt` as a group homomorphism of `A(ℚ̄)`. -/
noncomputable def semHom (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) : PtQ L A →+ PtQ L A :=
  MonoidHom.toAdditive (MonoidHom.mk' (semPt A σ τ hτσ G hG) (semPt_mul A σ τ hτσ G hG hμ))

/-- The underlying morphism of a point of `PtQ`. -/
noncomputable abbrev ptq (x : PtQ L A) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := ptl A (Additive.toMul x)

theorem ptq_ext {x y : PtQ L A} (h : ptq A x = ptq A y) : x = y :=
  Additive.toMul.injective (ptl_ext A h)

theorem semHom_ptq (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x : PtQ L A) :
    ptq A (semHom A σ τ hτσ G hG hμ x) = specA σ ≫ ptq A x ≫ G := rfl

theorem endPt_ptq (f : PkgI3.AbVar.End A) (x : PtQ L A) :
    ptq A (endPt A Qbar f x) = ptq A x ≫ f.hom.left := rfl

theorem zsmul_ptq (e : ℤ) (x : PtQ L A) :
    ptq A (e • x) = ptq A x ≫ (e : PkgI3.AbVar.End A).hom.left := by
  have h1 : endPt A Qbar (e : PkgI3.AbVar.End A) x = e • x := by
    rw [map_intCast, AddMonoid.End.intCast_apply]
  rw [← h1, endPt_ptq]

theorem galAct_ptq (σ' : Qbar ≃ₐ[L] Qbar) (x : PtQ L A) :
    ptq A (MonoidHom.toAdditive (A.galAct σ') x) =
      Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) ≫ ptq A x := rfl

end Pts

/-- **Level 1 (proved): the points bookkeeping.** σ-semilinear isogenies on `A/L` give the maps
`m_σ(x) = F_σ ∘ x ∘ Spec σ` with all clauses of `ConjIsogMapsAt`. -/
theorem conjIsogMapsAt_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) (hF : SemilinearIsogAt L A ι' F) :
    ∃ m : GQ → (PtQ L A →+ PtQ L A), ConjIsogMapsAt L A ι' m := by
  choose τ hτσ hτ hμ using fun σ => (hF σ).1
  let m : GQ → (PtQ L A →+ PtQ L A) := fun σ => semHom A σ (τ σ) (hτσ σ) (F σ) (hτ σ) (hμ σ)
  have hm : ∀ σ x, ptq A (m σ x) = specA σ ≫ ptq A x ≫ F σ := fun σ x => rfl
  refine ⟨m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 1: the Galois action on `G_L`
    intro σ σ' hσ'
    have hσL : σ ∈ GQL L := mem_GQL.mpr fun x hx => by
      rw [← hσ' x]; exact σ'.commutes ⟨x, hx⟩
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    have hσσ : specA σ = Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) := by
      rw [specA]; congr 1; ext z; exact (hσ' z).symm
    rw [hm, galAct_ptq, ((hF σ).2.2.2.2.1 σ hσL).1, Category.comp_id, hσσ]
  · -- clause 2: inflation
    intro σ k hk
    obtain ⟨h1, h2, h3⟩ := (hF σ).2.2.2.2.1 k hk
    refine ⟨AddMonoidHom.ext fun x => ptq_ext A ?_, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    · show ptq A (m (σ * k) x) = ptq A (m σ (m k x))
      rw [hm, hm, hm, h2, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
    · show ptq A (m (k * σ) x) = ptq A (m k (m σ x))
      rw [hm, hm, hm, h3, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
  · -- clause 3: `𝒪`-linearity
    intro σ a
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    show ptq A (m σ (endPt A Qbar (ι' a) x)) = ptq A (endPt A Qbar (ι' a) (m σ x))
    rw [hm, endPt_ptq, endPt_ptq, hm]
    simp only [Category.assoc]
    rw [(hF σ).2.1 a]
  · -- clause 4: surjective with finite kernel
    intro σ
    obtain ⟨-, -, hfin, hsurj, -, -⟩ := hF σ
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨x', hx'⟩ := hLift _ _ (F σ) hfin hsurj (ptq A y)
      have hiso : IsIso (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) :=
        ⟨⟨Spec.map (CommRingCat.ofHom ((τ σ).symm : L →+* L)), by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
          by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
             simp⟩⟩
      have hy : x' ≫ A.X.hom ≫ Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L)) =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [← hτ σ, ← Category.assoc, hx']; exact ptl_w A _
      have hx'' : x' ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
          inv (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) := by
        rw [← hy]; simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have hw : (specA σ⁻¹ ≫ x') ≫ A.X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [Category.assoc, hx'', ← Category.assoc, IsIso.comp_inv_eq, specA, ← Spec.map_comp,
          ← Spec.map_comp]
        congr 1
        ext z
        change act σ⁻¹ (z : Qbar) = ((τ σ z : L) : Qbar)
        rw [hτσ σ z]
      refine ⟨Additive.ofMul (Over.homMk (specA σ⁻¹ ≫ x') hw), ptq_ext A ?_⟩
      rw [hm]
      change specA σ ≫ (specA σ⁻¹ ≫ x') ≫ F σ = _
      rw [← Category.assoc, ← Category.assoc, specA_inv, Category.id_comp, hx']
    · have hsub : ((m σ).ker : Set (PtQ L A)) ⊆
          (fun x : PtQ L A => specA σ ≫ ptq A x) ⁻¹'
            {x' | x' ≫ F σ = ptq A (0 : PtQ L A)} := by
        intro x hx
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hx
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Category.assoc, ← hm, hx]
      refine Set.Finite.subset (Set.Finite.preimage ?_ (hFib _ _ (F σ) hfin _)) hsub
      intro x _ x₂ _ h
      exact ptq_ext A ((cancel_epi (specA σ)).mp h)
  · -- clause 5: the discrepancy
    intro σ τ'
    obtain ⟨e, he, δ, hδ⟩ := (hF σ).2.2.2.2.2 τ'
    refine ⟨e, he, δ, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    show ptq A (e • m σ (m τ' x)) = ptq A (endPt A Qbar δ (m (σ * τ') x))
    rw [zsmul_ptq, endPt_ptq, hm, hm, hm, specA_mul]
    simp only [Category.assoc]
    rw [hδ]
  · -- clause 6: algebraicity
    exact ⟨F, fun σ => ⟨(hF σ).2.2.1, (hF σ).2.2.2.1, fun x => hm σ x⟩⟩

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` and the two point lemmas (proved).** -/
theorem conjIsogMaps_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (h : SemilinearIsogMaps) : ConjIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨F, hF⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact conjIsogMapsAt_of_semilinear hLift hFib L _ _ F hF

/-- **`LiftQbarPoints` holds** (proved from Mathlib, `scratch/kf-glue/Points.lean`: the pullback of
`F` along `y` is a nonempty finite scheme `Spec B` over `Spec ℚ̄`; a maximal quotient of `B` is a
finite field extension of `ℚ̄`, hence `ℚ̄`, giving a section). -/
theorem liftQbarPoints : LiftQbarPoints := fun X Y F hF hs y =>
  KfGluePoints.liftQbar X Y F hF hs y

/-- **`FiniteFibreQbarPoints` holds** (proved from Mathlib: the points over `y` inject into the
sections of the finite `Spec B → Spec ℚ̄`, i.e. into `B →ₐ[ℚ̄] ℚ̄`, finite by Mathlib's
`Finite.algHom`). -/
theorem finiteFibreQbarPoints : FiniteFibreQbarPoints := fun X Y F hF y =>
  KfGluePoints.finiteFibreQbar X Y F hF y

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` alone (proved).** -/
theorem conjIsogMaps_of_semilinearIsogMaps (h : SemilinearIsogMaps) : ConjIsogMaps :=
  conjIsogMaps_of_semilinear liftQbarPoints finiteFibreQbarPoints h

/-- `KernelFieldExists` with `ConjIsogMaps` replaced by `SemilinearIsogMaps`. -/
theorem kernelFieldExists_of_semilinear (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hS : SemilinearIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_semilinearIsogMaps hS)

end G0ModField.KernelField

end KfGlueLevel1

/-! # kf-glue, part 3: `SemilinearIsogMaps`, level 2 — Skolem–Noether, the isogeny `ι(b)`, the
quasi-inverse and the discrepancy (proved)

`SemilinearIsogMaps` is proved from `SemilinearTwistIsos`: σ-semilinear scheme *automorphisms*
`E_σ` of `A/L` preserving the origin and the group law and twisting `ι` by some `α_σ ∈ Aut(𝒪)`
(A7's twisted QM isomorphisms `(A, ι∘α) ≅ (^σA, ^σι)`, descended to `L`), plus `MulIsogeny`
(mul-rigidity: from `KerUnitOpen` or two cotangent glue statements) and `RigidityHom` (proved).
Then `F_σ = E_σ ≫ ι(b_σ)` with `b_σ ∈ 𝒪` from Skolem–Noether (`aut_O_inner`), `ι(b)` is an isogeny
with quasi-inverse `ι(N b⁻¹)` (so no quasi-inverse leaf is needed), and the discrepancy is
`δ = ι(b_σ) ι(α_σ b_τ) D ι(c)` with `D = E_{στ}⁻¹ E_τ E_σ ∈ End_L(A)` (rigidity). -/

section KfGlueLevel2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

/- `G0FibreSimple.MulIsogeny` is in Part MR (MulRigidity.lean L321-323, verbatim). -/

namespace G0ModField.KernelField

open G0ModField

/-- **The core geometric glue: A7's twisted isomorphisms, descended to `L`, as σ-semilinear
automorphisms.** For each `σ ∈ G_ℚ` an automorphism `E_σ` of the scheme `A` lying over
`Spec(σ⁻¹|_L)`, preserving the group law and the origin, with `ι(a) E_σ = E_σ ι(α_σ a)` for an
`α_σ ∈ Aut(𝒪)`; `E_k = id`, `α_k = id` on `G_L`, and `E`, `α` constant on cosets of `G_L`. -/
def SemilinearTwistAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O)) : Prop :=
  ∀ σ : GQ,
    IsIso (E σ) ∧
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : E σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (E σ) (E σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E σ = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E σ = E σ ≫ (ι' (α σ a)).hom.left) ∧
    (∀ k ∈ GQL L, E k = 𝟙 _ ∧ α k = RingEquiv.refl O ∧ E (σ * k) = E σ ∧ E (k * σ) = E σ ∧
      α (σ * k) = α σ ∧ α (k * σ) = α σ)

/-- **`SemilinearIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`. -/
def SemilinearTwistIsos : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
          SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) E α

/-! ### Algebra in `𝒪` -/

/-- Skolem–Noether, linear form: for `α ∈ Aut 𝒪` there is `b ≠ 0` with `b α(a) = a b`. -/
theorem exists_b (α : O ≃+* O) : ∃ b : O, b ≠ 0 ∧ ∀ a : O, b * α a = a * b := by
  obtain ⟨u, hu⟩ := aut_O_inner α
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((u⁻¹ : Bˣ) : B)
  let b : O := ⟨(N : B) * (u⁻¹ : Bˣ), hmem⟩
  refine ⟨b, fun hb => ?_, fun a => ?_⟩
  · have h0 := congrArg Subtype.val hb
    change (N : B) * (u⁻¹ : Bˣ) = 0 at h0
    have h1 := congrArg (· * (u : B)) h0
    simp only [_root_.mul_assoc, Units.inv_mul, _root_.mul_one, zero_mul] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    omega
  · apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hu a]
    show (N : B) * (u⁻¹ : Bˣ) * (u * a * (u⁻¹ : Bˣ)) = a * ((N : B) * (u⁻¹ : Bˣ))
    have hc : ((u⁻¹ : Bˣ) : B) * (u * a * (u⁻¹ : Bˣ)) = a * (u⁻¹ : Bˣ) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [_root_.mul_assoc, hc, ← _root_.mul_assoc, (Nat.cast_commute N (a : B)).eq,
      _root_.mul_assoc]

/-- A quasi-inverse in `𝒪`: for `b ≠ 0` there are `c` and `N > 0` with `c b = N = b c`. -/
theorem exists_quasi_inv {b : O} (hb : b ≠ 0) :
    ∃ c : O, ∃ N : ℕ, 0 < N ∧ c * b = (N : O) ∧ b * c = (N : O) := by
  have hb' : (b : B) ≠ 0 := fun h => hb (Subtype.ext h)
  obtain ⟨v, hv⟩ := G0FibreSimple.B6_isUnit (b : B) hb'
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((v⁻¹ : Bˣ) : B)
  refine ⟨⟨(N : B) * (v⁻¹ : Bˣ), hmem⟩, N, hN, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subring.coe_mul]
    show (N : B) * (v⁻¹ : Bˣ) * b = ((N : O) : B)
    rw [← hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]; rfl
  · rw [Subring.coe_mul]
    show (b : B) * ((N : B) * (v⁻¹ : Bˣ)) = ((N : O) : B)
    rw [← hv, ← _root_.mul_assoc, (Nat.cast_commute N (v : B)).eq.symm, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]; rfl

/-- **`ι(b)` is an isogeny for `b ≠ 0`** (from `MulIsogeny`; `ι(c) ι(b) = [N] = ι(b) ι(c)`). -/
theorem iota_isogeny (hMul : G0FibreSimple.MulIsogeny) {k : Type} [Field k] [CharZero k]
    {A : PkgI3.AbVar k} (ι' : O →+* PkgI3.AbVar.End A) {b : O} (hb : b ≠ 0) :
    IsFinite (ι' b).hom.left ∧ Surjective (ι' b).hom.left := by
  obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv hb
  have hNz : ((N : ℤ) : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨hfin, hsurj⟩ := hMul k A (N : ℤ) hNz
  have e1 : (ι' b).hom.left ≫ (ι' c).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' c * ι' b = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  have e2 : (ι' c).hom.left ≫ (ι' b).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' b * ι' c = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hbc, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have : IsFinite ((ι' b).hom.left ≫ (ι' c).hom.left) := by rw [e1]; exact hfin
    have : IsSeparated (ι' c).hom.left := by
      have : IsSeparated ((ι' c).hom.left ≫ A.X.hom) := by rw [Over.w]; infer_instance
      exact IsSeparated.of_comp (ι' c).hom.left A.X.hom
    exact IsFinite.of_comp (ι' b).hom.left (ι' c).hom.left
  · have hs : Surjective ((ι' c).hom.left ≫ (ι' b).hom.left) := by rw [e2]; exact hsurj
    refine ⟨fun z => ?_⟩
    obtain ⟨w, hw⟩ := ((ι' c).hom.left ≫ (ι' b).hom.left).surjective z
    exact ⟨(ι' c).hom.left w, by rw [← Scheme.Hom.comp_apply]; exact hw⟩

/-! ### The assembly -/

theorem spec_comp_spec {L : IF} (a b c : L ≃+* L) (h : ∀ x, c x = a (b x)) :
    Spec.map (CommRingCat.ofHom (a : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (b : L →+* L)) =
      Spec.map (CommRingCat.ofHom (c : L →+* L)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  show a (b x) = c x
  exact (h x).symm

/-- **Level 2 (proved).** `SemilinearTwistAt` + `MulIsogeny` + `RigidityHom` ⟹ `SemilinearIsogAt`. -/
theorem semilinearIsogAt_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (L : IF) (A : PkgI3.AbVar L)
    (ι' : O →+* PkgI3.AbVar.End A) (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O))
    (h : SemilinearTwistAt L A ι' E α) : ∃ F : GQ → (A.X.left ⟶ A.X.left), SemilinearIsogAt L A ι' F := by
  classical
  choose bOf hbOf0 hbOf using exists_b
  let b : GQ → O := fun σ => if α σ = RingEquiv.refl O then 1 else bOf (α σ)
  have hb0 : ∀ σ, b σ ≠ 0 := fun σ => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true]; exact O_nontrivial
    · simp only [b, hσ, ite_false]; exact hbOf0 _
  have hb : ∀ σ a, b σ * α σ a = a * b σ := fun σ a => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true, RingEquiv.refl_apply, _root_.one_mul, _root_.mul_one]
    · simp only [b, hσ, ite_false]; exact hbOf _ a
  choose hiso τ hτσ hτ hμ hη using fun σ => And.intro (h σ).1 (h σ).2.1
  have htw := fun σ => (h σ).2.2.1
  have hk := fun σ => (h σ).2.2.2
  let F : GQ → (A.X.left ⟶ A.X.left) := fun σ => E σ ≫ (ι' (b σ)).hom.left
  have hFτ : ∀ σ, F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) :=
    fun σ => by
      simp only [F, Category.assoc]
      rw [Over.w (ι' (b σ)).hom, hτ σ]
  -- twist relation, pushed through `ι(x)`
  have htwx : ∀ σ (x : O), (ι' x).hom.left ≫ E σ = E σ ≫ (ι' (α σ x)).hom.left := fun σ x =>
    htw σ x
  -- composite of `ι`'s
  have hcomp : ∀ x y : O, (ι' x).hom.left ≫ (ι' y).hom.left = (ι' (y * x)).hom.left := by
    intro x y; rw [map_mul]; rfl
  refine ⟨F, fun σ => ⟨⟨τ σ, hτσ σ, hFτ σ, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- group law
    have hf : μ[A.X].left ≫ (ι' (b σ)).hom.left =
        ((ι' (b σ)).hom ⊗ₘ (ι' (b σ)).hom).left ≫ μ[A.X].left := by
      rw [← Over.comp_left, IsMonHom.mul_hom, Over.comp_left]
    show μ[A.X].left ≫ E σ ≫ (ι' (b σ)).hom.left = _
    rw [← Category.assoc, hμ σ, Category.assoc, hf, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [F, Over.tensorHom_left]
    · simp [F, Over.tensorHom_left]
  · -- `𝒪`-linearity
    intro a
    show (ι' a).hom.left ≫ E σ ≫ (ι' (b σ)).hom.left = (E σ ≫ (ι' (b σ)).hom.left) ≫ (ι' a).hom.left
    rw [← Category.assoc, htwx, Category.assoc, Category.assoc, hcomp, hcomp, hb]
  · -- finite
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).1
    show IsFinite (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- surjective
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).2
    show Surjective (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- inflation from `Gal(L/ℚ)`
    intro k hkL
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk σ k hkL
    have hbk : b k = 1 := by simp only [b, h2, ite_true]
    have hbσk : b (σ * k) = b σ := by simp only [b, h5]
    have hbkσ : b (k * σ) = b σ := by simp only [b, h6]
    refine ⟨?_, ?_, ?_⟩
    · show E k ≫ (ι' (b k)).hom.left = 𝟙 _
      rw [h1, hbk, map_one, Category.id_comp]; rfl
    · show E (σ * k) ≫ (ι' (b (σ * k))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h3, hbσk]
    · show E (k * σ) ≫ (ι' (b (k * σ))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h4, hbkσ]
  · -- the discrepancy
    intro ρ
    haveI := hiso (σ * ρ)
    -- `E_ρ E_σ` lies over `Spec τ_{σρ}`
    have hsp : Spec.map (CommRingCat.ofHom (τ ρ : L →+* L)) ≫
        Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) =
          Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L)) := by
      apply spec_comp_spec
      intro x
      apply Subtype.ext
      change ((τ (σ * ρ) x : L) : Qbar) = ((τ ρ (τ σ x) : L) : Qbar)
      rw [hτσ, hτσ, hτσ, mul_inv_rev, act_mul]
    haveI : IsIso (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) :=
      ⟨⟨Spec.map (CommRingCat.ofHom ((τ (σ * ρ)).symm : L →+* L)), by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
        by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
           simp⟩⟩
    let Dl : A.X.left ⟶ A.X.left := inv (E (σ * ρ)) ≫ E ρ ≫ E σ
    have hDw : Dl ≫ A.X.hom = A.X.hom := by
      have e1 : inv (E (σ * ρ)) ≫ A.X.hom =
          A.X.hom ≫ inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) := by
        rw [IsIso.eq_comp_inv, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc]
      simp only [Dl, Category.assoc]
      rw [hτ σ, reassoc_of% (hτ ρ), hsp, reassoc_of% e1, IsIso.inv_hom_id, Category.comp_id]
    let D : A.X ⟶ A.X := Over.homMk Dl hDw
    have hDη : η[A.X] ≫ D = η[A.X] := by
      apply Over.OverMorphism.ext
      have e2 : η[A.X].left ≫ inv (E (σ * ρ)) =
          inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) ≫ η[A.X].left := by
        rw [IsIso.comp_inv_eq, Category.assoc, hη, IsIso.inv_hom_id_assoc]
      rw [Over.comp_left]
      show η[A.X].left ≫ inv (E (σ * ρ)) ≫ E ρ ≫ E σ = η[A.X].left
      rw [reassoc_of% e2, reassoc_of% (hη ρ), hη σ, reassoc_of% hsp, IsIso.inv_hom_id_assoc]
    haveI : IsMonHom D := hR L A A D hDη
    let Dm : PkgI3.AbVar.End A := PkgI3.AbVar.Hom.mk' D
    obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv (hb0 (σ * ρ))
    let Y : PkgI3.AbVar.End A := ι' (b σ) * ι' (α σ (b ρ)) * Dm
    refine ⟨(N : ℤ), by exact_mod_cast hN.ne', Y * ι' c, ?_⟩
    -- left side: `E_ρ ι(b_ρ) E_σ ι(b_σ) [N] = E_{σρ} D ι(α_σ b_ρ) ι(b_σ) [N]`
    have hL : F ρ ≫ F σ = E (σ * ρ) ≫ Y.hom.left := by
      show (E ρ ≫ (ι' (b ρ)).hom.left) ≫ E σ ≫ (ι' (b σ)).hom.left = _
      have hY : Y.hom.left = Dl ≫ (ι' (α σ (b ρ))).hom.left ≫ (ι' (b σ)).hom.left := rfl
      rw [hY, Category.assoc, reassoc_of% (htwx σ (b ρ))]
      simp only [Dl, Category.assoc, IsIso.hom_inv_id_assoc]
    have hNc : ((N : ℤ) : PkgI3.AbVar.End A) = ι' c * ι' (b (σ * ρ)) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    have hcomm : Y * ((N : ℤ) : PkgI3.AbVar.End A) = ((N : ℤ) : PkgI3.AbVar.End A) * Y :=
      (Int.cast_commute (N : ℤ) Y).eq.symm
    show F ρ ≫ F σ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left =
      (E (σ * ρ) ≫ (ι' (b (σ * ρ))).hom.left) ≫ (Y * ι' c).hom.left
    have e3 : ((N : ℤ) : PkgI3.AbVar.End A).hom.left ≫ Y.hom.left =
        Y.hom.left ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
      show (Y * ((N : ℤ) : PkgI3.AbVar.End A)).hom.left =
        (((N : ℤ) : PkgI3.AbVar.End A) * Y).hom.left
      rw [hcomm]
    rw [← Category.assoc, hL, Category.assoc, ← e3, hNc]
    show E (σ * ρ) ≫ ((ι' (b (σ * ρ))).hom.left ≫ (ι' c).hom.left) ≫ Y.hom.left = _
    simp only [Category.assoc]
    rfl

/-- **Sanity check (proved): `SemilinearTwistAt` is satisfiable** — over `L = ℚ`, `E_σ = 𝟙`,
`α_σ = id`, `τ = id`, for any abelian variety and any `ι'`. -/
theorem semilinearTwistAt_bot (A : PkgI3.AbVar (⊥ : IF)) (ι' : O →+* PkgI3.AbVar.End A) :
    SemilinearTwistAt ⊥ A ι' (fun _ => 𝟙 _) (fun _ => RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl (⊥ : IF) : (⊥ : IF) ≃+* (⊥ : IF)) :
      (⊥ : IF) →+* (⊥ : IF))) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  intro σ
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => ?_, ?_, ?_, ?_⟩, fun a => ?_, fun k _ => ?_⟩
  · obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
    show (x : Qbar) = act σ⁻¹ (x : Qbar)
    rw [← hq]; exact ((act σ⁻¹).commutes q).symm
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SemilinearIsogMaps` from `SemilinearTwistIsos`, `MulIsogeny` and `RigidityHom` (proved). -/
theorem semilinearIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (h : SemilinearTwistIsos) : SemilinearIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨E, α, hE⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact semilinearIsogAt_of_twist hMul hR L _ _ E α hE

/-- **`ConjIsogMaps` from `SemilinearTwistIsos` and `MulIsogeny` (proved; `RigidityHom` and the
point lemmas are theorems).** -/
theorem conjIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny) (h : SemilinearTwistIsos) :
    ConjIsogMaps :=
  conjIsogMaps_of_semilinearIsogMaps
    (semilinearIsogMaps_of_twist hMul G0FibreSimple.rigidityHom h)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `SemilinearTwistIsos`. -/
theorem kernelFieldExists_of_twist (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hS : SemilinearTwistIsos) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_twist hMul hS)

end G0ModField.KernelField

end KfGlueLevel2

/-! # kf-glue, part 4: `SemilinearTwistIsos`, level 3 — A7 on the conjugates (proved)

`SemilinearTwistIsos` is proved from `TwistDescent`, a statement with no moduli content: for an
abelian variety `B` with a ring map `ι : 𝒪 → End B` over a Galois number field `K ⊆ ℚ̄` and a Hom
field `L ⊇ K` (`G_L` fixes every homomorphism between the conjugates `B_e = B ×_{K,e} ℚ̄`), if any
two conjugates are isomorphic over `ℚ̄` by an isomorphism twisting `ι` by some `α ∈ Aut 𝒪`, then
`B_L` has σ-semilinear twisted automorphisms `E_σ` (`SemilinearTwistAt`). This is Galois descent
from `ℚ̄` to `L` plus the bookkeeping of conjugate varieties. The hypothesis is proved for the
rational fibre `PK`: A7 in the manuscript's form (`LeafQM.AV.conj_iso_of_rational`, from R1fp and
R2fp) gives twisted QM isomorphisms between the base changes `Q_e` of `PK` along `e`, and
`IsBaseChangeOf` + rigidity (`rigidityHom`) identify `Q_e` with the conjugate `B_e` as abelian
varieties with `𝒪`-action. -/

section KfGlueLevel3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- Base change of an endomorphism of `B/K` to the conjugate `B_e = B ×_{K,e} ℚ̄`. -/
noncomputable def bcEnd (K : IF) (B : PkgI3.AbVar K) (e : K →ₐ[ℚ] Qbar)
    (f : PkgI3.AbVar.End B) : PkgI3.AbVar.End ((G4WeilRes.conjData K B).A e) :=
  @PkgI3.AbVar.Hom.mk' Qbar _ ((G4WeilRes.conjData K B).A e) ((G4WeilRes.conjData K B).A e)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar))))
      (f := f.hom))

/-- **Glue (Galois descent of twisted isomorphisms; no moduli content).** For `B/K` with
`ι : 𝒪 → End B`, `K ⊆ L ⊆ ℚ̄` finite Galois with `L` a Hom field of `B` (`G_L` acts trivially on
the Hom lattice of the conjugates), if any two conjugates `B_{e₁}`, `B_{e₂}` are isomorphic over `ℚ̄`
by an isomorphism `φ` with `ι_{e₁}(α a) φ = φ ι_{e₂}(a)` for some `α ∈ Aut 𝒪`, then `B_L` has the
σ-semilinear twisted automorphisms of `SemilinearTwistAt` for `ι_L = endBC ∘ ι`.
*Argument* (model check): for `σ ∈ G_ℚ` let `Ē_σ = φ ≫ cmp_σ` on `B_{ℚ̄} = B_{K.val}` (`φ` the
twisted isomorphism `B_{K.val} → B_{σ⁻¹ K.val}`, chosen on representatives of `G_ℚ/G_L` with
`φ = id` on `G_L`, and `cmp` the comparison of `G4Conj` over `Spec σ⁻¹`); it is σ-semilinear,
preserves the group law and the origin, and twists `ι`. Since `L` is a Hom field, `φ` is fixed by
conjugation through `G_L`, so `Ē_σ` commutes with the descent datum of `B_{ℚ̄}/B_L`; Galois descent
for morphisms (Mathlib: the fpqc topology is subcanonical, `Sites/Fpqc.lean`, with
`morphismsDescend` to reach a finite Galois `L'/L`) gives `E_σ` on `B_L`. -/
def TwistDescent : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hKL : K ≤ L),
    (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1) →
    (∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom) →
    ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
      SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) E α

/-- **The standard theorem behind `TwistDescent` (statement only; not used in any proof).**
Galois descent of morphisms along `ℚ̄/L`: for `L ⊆ ℚ̄` a number field, `X` quasi-compact and
quasi-separated and `Y` locally of finite presentation over `L`, every `ℚ̄`-morphism
`φ : X_ℚ̄ → Y_ℚ̄` fixed by conjugation through `G_L` (`G4Conj.conj`, as in `HomDescends`) is the base
change of a unique `L`-morphism. (SGA 1 VIII; Stacks, descent along fpqc coverings; locators
UNVERIFIED.) In the project: `morphismsDescend` (EGA IV 8.8.2, proved) descends `φ` to a finite
`L'`; Mathlib's `EffectiveEpi` for flat surjective quasi-compact morphisms (`Sites/Fpqc.lean`)
then needs `L' ⊗_L L' ≅ ∏_{Gal(L'/L)} L'` (not in Mathlib v4.35). `TwistDescent` follows from this
statement applied to the σ-semilinear maps `Ē_σ` (after identifying them with maps out of `^σB_L`)
together with the conjugate bookkeeping; that deduction is a model check, not compiled. -/
def GaloisDescentMor : Prop :=
  ∀ (L : IF) [FiniteDimensional ℚ L] (X Y : Over (Spec (CommRingCat.of L)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (φ : (Over.pullback (G4WeilRes.specIncl L)).obj X ⟶ (Over.pullback (G4WeilRes.specIncl L)).obj Y),
    (∀ σ ∈ L.fixingSubgroup,
      ∀ hf : G4WeilRes.specIncl L = G4WeilRes.specGal σ ≫ G4WeilRes.specIncl L,
        G4Conj.conj X Y (G4WeilRes.specGal σ) hf hf φ = φ) →
    ∃! ψ : X ⟶ Y, (Over.pullback (G4WeilRes.specIncl L)).map ψ = φ

/-- **Transport (proved, rigidity).** A base change `Q` of `PK` along `e : K → ℚ̄`
(`IsBaseChangeOf`, a pullback square compatible with `ι` and `η`) is isomorphic to the conjugate
`B_e` as an abelian variety with `𝒪`-action. -/
theorem bc_transport (hR : G0FibreSimple.RigidityHom) {K : IF} (PK : QML3 K)
    (e : K →ₐ[ℚ] Qbar) (Q : QML3 Qbar) (hb : IsBaseChangeOf (e : K →+* Qbar) PK Q) :
    ∃ (θ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e) Q.A)
      (θ' : PkgI3.AbVar.Hom Q.A ((G4WeilRes.conjData K PK.A).A e)),
      θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
      ∀ a : O, (bcEnd K PK.A e (PK.q.iota a)).hom ≫ θ.hom = θ.hom ≫ (Q.q.iota a).hom := by
  obtain ⟨g, hpb, hι, hη⟩ := hb
  let s := Spec.map (CommRingCat.ofHom (e : K →+* Qbar))
  let Ae : PkgI3.AbVar Qbar := (G4WeilRes.conjData K PK.A).A e
  have hpb0 : IsPullback (pullback.fst PK.A.X.hom s) (pullback.snd PK.A.X.hom s) PK.A.X.hom s :=
    IsPullback.of_hasPullback _ _
  let θ : pullback PK.A.X.hom s ≅ Q.A.X.left := hpb0.isoIsPullback _ _ hpb
  have hθfst : θ.hom ≫ g = pullback.fst PK.A.X.hom s := hpb0.isoIsPullback_hom_fst _ _ hpb
  have hθsnd : θ.hom ≫ Q.A.X.hom = pullback.snd PK.A.X.hom s :=
    hpb0.isoIsPullback_hom_snd _ _ hpb
  let h : Ae.X ⟶ Q.A.X := Over.homMk θ.hom hθsnd
  let hinv : Q.A.X ⟶ Ae.X := Over.homMk θ.inv ((Iso.inv_comp_eq θ).mpr hθsnd.symm)
  have hhi : h ≫ hinv = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.hom_inv_id
  have hih : hinv ≫ h = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.inv_hom_id
  have hu : ∀ {R : Type} [Field R] {U : Over (Spec (CommRingCat.of R))},
      (toUnit U).left = U.hom := fun {R _ U} => by
    have := Over.w (toUnit U); simpa using this
  have hid : ∀ (R : Type) [Field R], Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ :=
    fun R _ => by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hηQ : η[Q.A.X].left ≫ g = s ≫ η[PK.A.X].left := by
    have := hη 0
    have h0Q : Additive.toMul (Q.e.eta 0) = 1 := by rw [map_zero]; rfl
    have h0P : Additive.toMul (PK.e.eta 0) = 1 := by rw [map_zero]; rfl
    rw [h0Q, h0P] at this
    change (toUnit (PkgI3.AbVar.ptObj (K := Qbar) Qbar) ≫ η[Q.A.X]).left ≫ g =
      s ≫ (toUnit (PkgI3.AbVar.ptObj (K := K) K) ≫ η[PK.A.X]).left at this
    rw [Over.comp_left, Over.comp_left, hu, hu] at this
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, hid, Category.assoc] at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  have hηW : η[Ae.X].left ≫ pullback.fst PK.A.X.hom s = s ≫ η[PK.A.X].left := by
    have e1 := G4Conj.one_left_fst s PK.A.X
    erw [e1]
  have hunit : η[Ae.X] ≫ h = η[Q.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb.hom_ext
    · have hh : h.left ≫ g = pullback.fst PK.A.X.hom s := hθfst
      rw [Category.assoc, hh, hηW, hηQ]
    · rw [Category.assoc, Over.w h, Over.w η[Ae.X], Over.w η[Q.A.X]]
  have hunit' : η[Q.A.X] ≫ hinv = η[Ae.X] := by
    rw [← hunit, Category.assoc, hhi, Category.comp_id]
  haveI hmh : IsMonHom h := hR Qbar Ae Q.A h hunit
  haveI hmi : IsMonHom hinv := hR Qbar Q.A Ae hinv hunit'
  refine ⟨PkgI3.AbVar.Hom.mk' h, PkgI3.AbVar.Hom.mk' hinv, hhi, hih, fun a => ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply hpb.hom_ext
  · change ((Over.pullback s).map (PK.q.iota a).hom).left ≫ θ.hom ≫ g =
      θ.hom ≫ (Q.q.iota a).hom.left ≫ g
    rw [hι a, hθfst, ← Category.assoc θ.hom g, hθfst]
    exact pullback.lift_fst _ _ _
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [Over.w h, Over.w (Q.q.iota a).hom, Over.w h]
    exact Over.w (bcEnd K PK.A e (PK.q.iota a)).hom

/-- **A7 on the conjugates (proved).** For a `K`-point `yK` with object `PK` and rational
`π`-value, any two conjugates `PK.A_{e₁}`, `PK.A_{e₂}` are isomorphic over `ℚ̄` by an
isomorphism twisting `ι` by some `α ∈ Aut 𝒪`. -/
theorem conjTwist_of_rational (hR : G0FibreSimple.RigidityHom)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) {K : IF} (yK : fieldPt K ⟶ Y) (PK : QML3 K)
    (hyK : Φ K yK = M3.mk PK) (j₀ : ℚ)
    (hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) : ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₁) ((G4WeilRes.conjData K PK.A).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₂) ((G4WeilRes.conjData K PK.A).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K PK.A e₁ (PK.q.iota (α a))).hom ≫ φ.hom =
          φ.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by
  obtain ⟨Q₁, Q₂, hb₁, hb₂, α, ⟨f⟩⟩ := conj_iso_of_rational hR1 hR2 yK PK hyK j₀ hj e₁ e₂
  obtain ⟨θ₁, θ₁', h11, h12, hι1⟩ := bc_transport hR PK e₁ Q₁ hb₁
  obtain ⟨θ₂, θ₂', h21, h22, hι2⟩ := bc_transport hR PK e₂ Q₂ hb₂
  have hι2' : ∀ a : O, (Q₂.q.iota a).hom ≫ θ₂'.hom = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom :=
    fun a => by
      calc (Q₂.q.iota a).hom ≫ θ₂'.hom
          = θ₂'.hom ≫ θ₂.hom ≫ (Q₂.q.iota a).hom ≫ θ₂'.hom := by rw [reassoc_of% h22]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom ≫ θ₂.hom ≫ θ₂'.hom := by
            rw [reassoc_of% (hι2 a)]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by rw [h21, Category.comp_id]
  refine ⟨α, PkgI3.AbVar.Hom.mk' (θ₁.hom ≫ f.φ.hom ≫ θ₂'.hom),
    PkgI3.AbVar.Hom.mk' (θ₂.hom ≫ f.ψ.hom ≫ θ₁'.hom), ?_, ?_, fun a => ?_⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h22, reassoc_of% f.left, h11]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h12, reassoc_of% f.right, h21]
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    have hf : (Q₁.q.iota (α a)).hom ≫ f.φ.hom = f.φ.hom ≫ (Q₂.q.iota a).hom := f.equivariant a
    simp only [Category.assoc]
    rw [reassoc_of% (hι1 (α a)), reassoc_of% hf, hι2' a]

/-- **`SemilinearTwistIsos` from `TwistDescent` (proved; A7 and rigidity).** -/
theorem semilinearTwistIsos_of_descent (hD : TwistDescent) : SemilinearTwistIsos := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  have hyy : fieldMap K.val ≫ yK = y := (Φ Qbar).injective (hyKP.trans hy.symm)
  have hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀) := by
    have h2 : (π.val (K := K) yK.left).map (K.val : K →+* Qbar) =
        OnePoint.some (algebraMap ℚ Qbar j₀) := by
      have h1 := π.val_comp ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) yK.left
      rw [← hyy] at hπ
      exact h1.symm.trans hπ
    generalize π.val (K := K) yK.left = v at h2 ⊢
    induction v using OnePoint.rec with
    | infty => simp at h2
    | coe x =>
      rw [OnePoint.map_some] at h2
      have h3 : (K.val : K →+* Qbar) x = (K.val : K →+* Qbar) (algebraMap ℚ K j₀) := by
        rw [OnePoint.coe_eq_coe] at h2
        rw [h2]; exact (K.val.commutes j₀).symm
      rw [RingHom.injective _ h3]
  exact hD K PK.A PK.q.iota L hKL hfix
    (conjTwist_of_rational G0FibreSimple.rigidityHom hR1 hR2 yK PK hyK j₀ hj)

/-- **`ConjIsogMaps` from `TwistDescent` and `MulIsogeny` (proved).** -/
theorem conjIsogMaps_of_descent (hMul : G0FibreSimple.MulIsogeny) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_twist hMul (semilinearTwistIsos_of_descent hD)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `TwistDescent`. -/
theorem kernelFieldExists_of_descent (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hD : TwistDescent) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_descent hMul hD)

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` and `TwistDescent` (proved).** -/
theorem conjIsogMaps_of_kerUnitOpen (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_kerUnitOpen hK) hD

/-- **`ConjIsogMaps` from glue only (proved):** mul-rigidity's two cotangent glue statements and
`TwistDescent`. -/
theorem conjIsogMaps_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hD : TwistDescent) : ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_cotangent h1 h2) hD

/-- **`KernelFieldExists`, final form (proved).** Leaves: `HomFreeFinite` (T6),
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, `QMDichotomyYu` (T27),
`KerUnitOpen` (mul-rigidity; implied by the published `MulEtale`). Glue: FS5 `FibreComTrivial`
(g0-fibresimple) and `TwistDescent` (Galois descent). -/
theorem kernelFieldExists_of_kerUnitOpen (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_kerUnitOpen hK hD)

end G0ModField.KernelField

end KfGlueLevel3

#print axioms G0ModField.KernelField.conjIsogMapsAt_of_semilinear
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinear
#print axioms G0ModField.KernelField.liftQbarPoints
#print axioms G0ModField.KernelField.finiteFibreQbarPoints
#print axioms G0ModField.KernelField.conjIsogMaps_of_semilinearIsogMaps
#print axioms G0ModField.KernelField.kernelFieldExists_of_semilinear
#print axioms G0ModField.KernelField.semilinearIsogAt_of_twist
#print axioms G0ModField.KernelField.conjIsogMaps_of_twist
#print axioms G0ModField.KernelField.kernelFieldExists_of_twist
#print axioms G0ModField.KernelField.iota_isogeny
#print axioms G0ModField.KernelField.bc_transport
#print axioms G0ModField.KernelField.conjTwist_of_rational
#print axioms G0ModField.KernelField.semilinearTwistIsos_of_descent
#print axioms G0ModField.KernelField.conjIsogMaps_of_descent
#print axioms G0ModField.KernelField.kernelFieldExists_of_descent
#print axioms G0ModField.KernelField.conjIsogMaps_of_kerUnitOpen
#print axioms G0ModField.KernelField.conjIsogMaps_of_cotangent
#print axioms G0ModField.KernelField.kernelFieldExists_of_kerUnitOpen
#print axioms G0ModField.KernelField.semilinearTwistAt_bot

/-! ################################################################################
  twist-descent (new). Everything above is scratch/kf-glue/KfGlue.lean verbatim. -/

/-! # twist-descent, part XC: comparison maps between base changes along different bases

Generic category theory (any `C` with pullbacks), generalizing `G4Conj.cmp` (one base `T`) to two
bases: for `f₂ = s ≫ f₁` with `s : T₂ ⟶ T₁`, the comparison `X ×_{S,f₂} T₂ → X ×_{S,f₁} T₁`
(`xc`), its pullback square, composition, and compatibility with base-changed endomorphisms,
units and multiplications. -/

section TwistDescentXC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace TwistDescentXC

variable {C : Type*} [Category C] [HasPullbacks C] {S : C} (X : Over S)

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- `X ×_{f₂} T₂ → X ×_{f₁} T₁` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def xc {T₁ T₂ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

variable {T₁ T₂ T₃ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} {f₃ : T₃ ⟶ S}

@[reassoc (attr := simp)]
theorem xc_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s := pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem xc_isPullback (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    IsPullback (xc X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : xc X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [xc_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [xc_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

theorem xc_comp (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (h'' : f₃ = (s' ≫ s) ≫ f₁) : xc X s' h' ≫ xc X s h = xc X (s' ≫ s) h'' := by
  apply pullback.hom_ext <;> simp

theorem xc_comp_eq (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (t : T₃ ⟶ T₁) (ht : f₃ = t ≫ f₁) (hst : s' ≫ s = t) :
    xc X s' h' ≫ xc X s h = xc X t ht := by
  subst hst; exact xc_comp X s h s' h' ht

theorem xc_congr {s s' : T₂ ⟶ T₁} (hs : s = s') (h : f₂ = s ≫ f₁) (h' : f₂ = s' ≫ f₁) :
    xc X s h = xc X s' h' := by
  subst hs; rfl

theorem xc_self (s : T₁ ⟶ T₁) (hs : s = 𝟙 T₁) (h : f₁ = s ≫ f₁) : xc X s h = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [xc_snd, hs, Category.comp_id, Category.id_comp]

/-- `xc` intertwines base-changed endomorphisms. -/
theorem xc_map (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (f : X ⟶ X) :
    ((Over.pullback f₂).map f).left ≫ xc X s h = xc X s h ≫ ((Over.pullback f₁).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, xc_fst, Over.pullback_map_left, pullback.lift_fst, xc_fst_assoc]
  · simp only [Category.assoc, xc_snd, Over.pullback_map_left, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- `xc` on the self-products. -/
noncomputable def xc2 (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ xc X s h) (pullback.snd _ _ ≫ xc X s h) (by
    show (pullback.fst _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, xc_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem xc2_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ xc X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc2_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xc X s h :=
  pullback.lift_snd _ _ _

/-- **`xc` respects the multiplications.** -/
theorem xc_mul [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (μ[(Over.pullback f₂).obj X]).left ≫ xc X s h =
      xc2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, Category.assoc, G4Conj.mul_left_fst, G4Conj.mul_left_fst,
      ← Category.assoc (xc2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, xc2_fst_assoc, xc_fst]
    · simp only [Category.assoc, pullback.lift_snd, xc2_snd_assoc, xc_fst]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      xc2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [xc2_fst_assoc, xc_snd, Category.assoc]

/-- **`xc` respects the units.** -/
theorem xc_one [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (η[(Over.pullback f₂).obj X]).left ≫ xc X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, G4Conj.one_left_fst, Category.assoc, G4Conj.one_left_fst, h,
      Category.assoc]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end TwistDescentXC

end TwistDescentXC

/-! # twist-descent, part HFD: descent of `G_L`-invariant morphisms between conjugates

For a number field `K ⊆ ℚ̄`, an abelian variety `B/K`, a finite Galois `L ⊆ ℚ̄` and two embeddings
`e₁L, e₂L : K → L`, a `ℚ̄`-morphism `φ : B ×_{K,e₁} ℚ̄ → B ×_{K,e₂} ℚ̄` (`eᵢ = (L ↪ ℚ̄) ∘ eᵢL`) that
commutes with the Galois translates by `G_L` is the base change of a morphism
`B ×_{K,e₁L} L → B ×_{K,e₂L} L` (`hfd`). Proof: EGA IV₃ 8.8.2 (`MorphDescend.exists_descend`,
proved) descends `φ` to a finite `L₁ ⊇ L`; pass to the normal closure `L'` of `L₁`; the descended
morphism is `Gal(L'/L)`-invariant (checked after the epimorphism `B_{ℚ̄} → B_{L'}`), so it descends
to `L` by `TwistDescentGD.descend` (Galois descent along `L'/L`, from Mathlib's fpqc descent). -/

section TwistDescentHFD

open CategoryTheory AlgebraicGeometry Limits
open TwistDescentXC

namespace TwistDescentHFD

/-- `Spec` of a ring map. -/
noncomputable abbrev sp {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom f)

theorem sp_comp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp t ≫ sp s = sp u := by
  rw [sp, sp, sp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x

theorem sp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp u = sp t ≫ sp s :=
  (sp_comp_eq s t u h).symm

theorem sp_id_eq {R : Type} [CommRing R] (t : R →+* R) (h : ∀ x, t x = x) : sp t = 𝟙 _ := by
  rw [sp, ← Spec.map_id]
  congr 1
  ext x
  exact h x

abbrev Qb : Type := AlgebraicClosure ℚ

variable {K : IntermediateField ℚ Qb} (B : PkgI3.AbVar K)

/-- `ℚ̄ → B_{L'}` comparisons are epimorphisms (flat surjective quasi-compact base change). -/
theorem xc_epi {L : IntermediateField ℚ Qb} (eL : K →+* L) (e : K →+* Qb)
    (h : sp e = sp (algebraMap L Qb) ≫ sp eL) : Epi (xc B.X (sp (algebraMap L Qb)) h) :=
  TwistDescentGD.epi_of_isPullback_field (xc_isPullback B.X _ h)

/-- **Hom-field descent.** -/
theorem hfd {L : IntermediateField ℚ Qb} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (e₁L e₂L : K →+* L) (e₁ e₂ : K →+* Qb)
    (h₁ : sp e₁ = sp (algebraMap L Qb) ≫ sp e₁L) (h₂ : sp e₂ = sp (algebraMap L Qb) ≫ sp e₂L)
    (he₁ : ∀ x, (e₁L x : Qb) = e₁ x) (he₂ : ∀ x, (e₂L x : Qb) = e₂ x)
    (φ : pullback B.X.hom (sp e₁) ⟶ pullback B.X.hom (sp e₂))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _)
    (hinv : ∀ k : Qb ≃ₐ[ℚ] Qb, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁) (k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂),
        xc B.X (sp (k : Qb →+* Qb)) k₁ ≫ φ = φ ≫ xc B.X (sp (k : Qb →+* Qb)) k₂) :
    ∃ φL : pullback B.X.hom (sp e₁L) ⟶ pullback B.X.hom (sp e₂L),
      xc B.X (sp (algebraMap L Qb)) h₁ ≫ φL = φ ≫ xc B.X (sp (algebraMap L Qb)) h₂ := by
  have hm₁ : ∀ x, e₁ x ∈ L := fun x => he₁ x ▸ (e₁L x).2
  have hm₂ : ∀ x, e₂ x ∈ L := fun x => he₂ x ▸ (e₂L x).2
  obtain ⟨L₁, ψ, hψ⟩ := MorphDescend.exists_descend L B.X B.X e₁ e₂ hm₁ hm₂ φ hφ
  obtain ⟨L₁, hfin₁, hLL₁⟩ := L₁
  let L' : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ L₁ Qb
  have hL₁L' : L₁ ≤ L' := IntermediateField.le_normalClosure L₁
  have hLL' : L ≤ L' := hLL₁.trans hL₁L'
  let _ : Algebra L L' := G0ModField.incAlg hLL'
  have : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : FiniteDimensional ℚ L₁ := hfin₁
  have : FiniteDimensional ℚ L' := inferInstance
  have : IsGalois ℚ L' := inferInstance
  have : FiniteDimensional L L' := FiniteDimensional.right ℚ L L'
  have : IsGalois L L' := IsGalois.tower_top_of_isGalois ℚ L L'
  -- the maps at level `L'`
  let e₁' : K →+* L' := (algebraMap L L').comp e₁L
  have hq : sp e₁' = sp (algebraMap L L') ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  let q : pullback B.X.hom (sp e₁') ⟶ pullback B.X.hom (sp e₁L) := xc B.X (sp (algebraMap L L')) hq
  have hpb := xc_isPullback B.X (sp (algebraMap L L')) hq
  let r₁ := MorphDescend.restrL L e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩
  let r₂ := MorphDescend.restrL L e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩
  have ha : sp e₁' = sp (IntermediateField.inclusion hL₁L' : L₁ →+* L') ≫ sp r₁ :=
    sp_eq _ _ _ fun x => Subtype.ext (he₁ x).symm
  have hb : sp r₂ = sp (IntermediateField.inclusion hLL₁ : L →+* L₁) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => Subtype.ext (he₂ x)
  let f : pullback B.X.hom (sp e₁') ⟶ pullback B.X.hom (sp e₂L) :=
    xc B.X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha ≫ ψ ≫
      xc B.X (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb
  have hQ' : sp e₁ = sp (algebraMap L' Qb) ≫ sp e₁' := sp_eq _ _ _ fun x => (he₁ x)
  have hepi : Epi (xc B.X (sp (algebraMap L' Qb)) hQ') := xc_epi B e₁' e₁ hQ'
  -- `f` after `ℚ̄ → L'` is `φ ≫ (ℚ̄ → L)`
  have hfQ : xc B.X (sp (algebraMap L' Qb)) hQ' ≫ f = φ ≫ xc B.X (sp (algebraMap L Qb)) h₂ := by
    have c1 : xc B.X (sp (algebraMap L' Qb)) hQ' ≫
        xc B.X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha =
        MorphDescend.cmp L B.X e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩ :=
      xc_comp_eq B.X _ _ _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl)
        (sp_comp_eq _ _ _ fun _ => rfl)
    have c2 : MorphDescend.cmp L B.X e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩ ≫
        xc B.X (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb =
        xc B.X (sp (algebraMap L Qb)) h₂ :=
      xc_comp_eq B.X _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl) _ _
        (sp_comp_eq _ _ _ fun _ => rfl)
    simp only [f]
    rw [← Category.assoc, c1, ← reassoc_of% hψ, c2]
  obtain ⟨φL, hφL⟩ := TwistDescentGD.descend hpb f (fun g => by
    have hc : sp e₁' = sp (g : L' →+* L') ≫ sp e₁' :=
      sp_eq _ _ _ fun x => g.commutes (e₁L x)
    refine ⟨xc B.X (sp (g : L' →+* L')) hc, ?_, xc_snd _ _ _, ?_⟩
    · exact xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => g.commutes y)
    · -- lift `g` to `k ∈ G_ℚ`
      obtain ⟨k, hk⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L') (E := Qb)
        (g.restrictScalars ℚ)
      have hkx : ∀ x : L', k (x : Qb) = (g x : Qb) := fun x => by
        rw [← AlgEquiv.restrictNormalHom_apply L' k x, hk]; rfl
      have hkL : k ∈ L.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        have := hkx (algebraMap L L' ⟨y, hy⟩)
        rw [g.commutes] at this
        exact this
      have hkL' : ∀ y : L, k (y : Qb) = y := fun y =>
        (IntermediateField.mem_fixingSubgroup_iff L k).mp hkL y y.2
      have k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁ :=
        sp_eq _ _ _ fun x => by rw [← he₁ x]; exact hkL' _
      have k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂ :=
        sp_eq _ _ _ fun x => by rw [← he₂ x]; exact hkL' _
      have hu : sp e₁ = sp ((algebraMap L' Qb).comp (g : L' →+* L')) ≫ sp e₁' :=
        sp_eq _ _ _ fun x => by
          show ((g (algebraMap L L' (e₁L x)) : L') : Qb) = e₁ x
          rw [g.commutes]; exact he₁ x
      have c4 : xc B.X (sp (algebraMap L' Qb)) hQ' ≫ xc B.X (sp (g : L' →+* L')) hc =
          xc B.X (sp (k : Qb →+* Qb)) k₁ ≫ xc B.X (sp (algebraMap L' Qb)) hQ' :=
        (xc_comp_eq B.X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun _ => rfl)).trans
          (xc_comp_eq B.X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun x => hkx x)).symm
      have c5 : xc B.X (sp (k : Qb →+* Qb)) k₂ ≫ xc B.X (sp (algebraMap L Qb)) h₂ =
          xc B.X (sp (algebraMap L Qb)) h₂ :=
        xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => hkL' y)
      rw [← cancel_epi (xc B.X (sp (algebraMap L' Qb)) hQ'), ← Category.assoc, c4,
        Category.assoc, hfQ, ← Category.assoc, hinv k hkL k₁ k₂, Category.assoc, c5])
  refine ⟨φL, ?_⟩
  have c3 : xc B.X (sp (algebraMap L Qb)) h₁ = xc B.X (sp (algebraMap L' Qb)) hQ' ≫ q :=
    (xc_comp_eq B.X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun _ => rfl)).symm
  rw [c3, Category.assoc, hφL, hfQ]

end TwistDescentHFD

end TwistDescentHFD

/-! # twist-descent, part MAIN: `TwistDescent` (kf-glue) proved

For `σ ∈ G_ℚ` with restriction `ρ = σ|_L`: the hypothesis gives a twisted isomorphism
`φ : B_{e₀} ≅ B_{σ⁻¹e₀}` over `ℚ̄` (`e₀ : K ↪ ℚ̄`); it is `G_L`-invariant (`L` is a Hom field,
`td_hom_inv`), so it descends to `φ_L : B_L → B ×_{K,τ∘(K↪L)} L` (`hfd`, `τ = σ⁻¹|_L`); then
`E = φ_L ≫ c_τ`, with `c_τ` the comparison over `Spec τ`. `φ_L` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`, proved in kf-glue). `E` and `α` are chosen as functions of `σ|_L`,
with `E = 𝟙`, `α = id` on the trivial class (`twistDescent`). -/

section TwistDescentMain

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`G_L` fixes homomorphisms between conjugates** (from the Hom-field hypothesis of
`TwistDescent`): `k ∘ φ = φ ∘ k` for `k ∈ G_L` and `φ : B_{e₁} → B_{e₂}`. -/
theorem td_hom_inv {K : IF} [IsGalois ℚ K] (B : PkgI3.AbVar K) {L : IF} (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
    (k : Qbar ≃ₐ[ℚ] Qbar) (hk : k ∈ L.fixingSubgroup)
    (k₁ : sp (e₁ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₁ : K →+* Qbar))
    (k₂ : sp (e₂ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₂ : K →+* Qbar)) :
    xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
      φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
  classical
  have hs : ∀ e : K →ₐ[ℚ] Qbar, (G4WeilRes.embAct K k).symm e = e := by
    intro e
    ext x
    have hx : e x ∈ L :=
      hKL ((SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal e) (e x)).mp ⟨x, rfl⟩)
    exact (IntermediateField.mem_fixingSubgroup_iff L _).mp (inv_mem hk) _ hx
  let m : G4WeilRes.HomLattice (G4WeilRes.conjData K B).A := Pi.single (e₁, e₂) φ
  have hm : G4WeilRes.conjAct K B k m = m := LinearEquiv.congr_fun (hHF k hk) m
  have h0 := G4WeilRes.conjAct_isConjAction K B k m e₁ e₂
  dsimp only at h0
  rw [hm] at h0
  have hme : m (e₁, e₂) = φ := Pi.single_eq_same _ _
  rw [hme] at h0
  have gen : ∀ (x y : K →ₐ[ℚ] Qbar) (hx : x = e₁) (hy : y = e₂)
      (p₁ : G4WeilRes.specEmb K e₁ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K x)
      (p₂ : G4WeilRes.specEmb K e₂ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K y),
      φ.hom.left ≫ G4Conj.cmp B.X (G4WeilRes.specGal k) p₂ =
        G4Conj.cmp B.X (G4WeilRes.specGal k) p₁ ≫ (m (x, y)).hom.left →
      xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
        φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
    intro x y hx hy p₁ p₂ h
    subst hx hy
    rw [hme] at h
    exact h.symm
  exact gen _ _ (hs e₁) (hs e₂) (G4WeilRes.specEmb_symm K k e₁) (G4WeilRes.specEmb_symm K k e₂) h0

/-- The clauses of `SemilinearTwistAt` at one `σ`, in terms of `ρ = σ|_L`. -/
def TwistClause (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) (ρ : L ≃ₐ[ℚ] L)
    (E : A.X.left ⟶ A.X.left) (α : O ≃+* O) : Prop :=
  IsIso E ∧
    (∃ τ : L ≃+* L, (∀ x : L, τ x = ρ⁻¹ x) ∧
      ∃ hτ : E ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom E E
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E = E ≫ (ι' (α a)).hom.left)

/-- `Spec ℚ̄ → Spec L` is an epimorphism. -/
theorem specQbar_epi (L : IF) : Epi (sp (algebraMap L Qbar)) := by
  obtain ⟨h1, h2, h3⟩ := TwistDescentGD.spec_field_props L Qbar
  infer_instance

/-- The trivial class: `E = 𝟙`, `α = id`. -/
theorem twistClause_one (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) :
    TwistClause L A ι' 1 (𝟙 _) (RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl L : L ≃+* L) : L →+* L)) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => rfl, ?_, ?_, ?_⟩, fun a => ?_⟩
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp

set_option maxHeartbeats 1000000 in
/-- **The construction at one `σ`** (`E = φ_L ≫ c_τ`, `α = α_φ⁻¹`). -/
theorem td_construct {K : IF} [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (hTw : ∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) (AlgEquiv.restrictNormalHom L σ) E α := by
  letI : Algebra K L := incAlg hKL
  let e₀ : K →ₐ[ℚ] Qbar := K.val
  let e₂ : K →ₐ[ℚ] Qbar := G4WeilRes.embAct K σ⁻¹ e₀
  obtain ⟨α, φ, ψ, hφψ, hψφ, htw⟩ := hTw e₀ e₂
  let τ : L ≃+* L := (AlgEquiv.restrictNormalHom L σ⁻¹ : L ≃ₐ[ℚ] L).toRingEquiv
  have hτx : ∀ x : L, (τ x : Qbar) = σ⁻¹ x := fun x => AlgEquiv.restrictNormalHom_apply L σ⁻¹ x
  let e₁L : K →+* L := algebraMap K L
  let e₂L : K →+* L := (τ : L →+* L).comp e₁L
  have he₁ : ∀ x, (e₁L x : Qbar) = (e₀ : K →+* Qbar) x := fun x => rfl
  have he₂ : ∀ x, (e₂L x : Qbar) = (e₂ : K →+* Qbar) x := fun x => hτx _
  have h₁ : sp (e₀ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₁L := sp_eq _ _ _ he₁
  have h₂ : sp (e₂ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₂L := sp_eq _ _ _ he₂
  let φ₀ : pullback B.X.hom (sp (e₀ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₂ : K →+* Qbar)) :=
    φ.hom.left
  let ψ₀ : pullback B.X.hom (sp (e₂ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₀ : K →+* Qbar)) :=
    ψ.hom.left
  have hφs : φ₀ ≫ pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) := Over.w φ.hom
  have hψs : ψ₀ ≫ pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) := Over.w ψ.hom
  obtain ⟨φL, hφL⟩ := hfd B e₁L e₂L _ _ h₁ h₂ he₁ he₂ φ₀ hφs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₀ e₂ φ k hk k₁ k₂)
  obtain ⟨ψL, hψL⟩ := hfd B e₂L e₁L _ _ h₂ h₁ he₂ he₁ ψ₀ hψs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₂ e₀ ψ k hk k₁ k₂)
  have ep₁ := xc_epi B e₁L _ h₁
  have ep₂ := xc_epi B e₂L _ h₂
  have hφψ' : φ₀ ≫ ψ₀ = 𝟙 _ := congrArg Over.Hom.left hφψ
  have hψφ' : ψ₀ ≫ φ₀ = 𝟙 _ := congrArg Over.Hom.left hψφ
  have hφψL : φL ≫ ψL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, hψL, ← Category.assoc, hφψ', Category.id_comp, Category.comp_id]
  have hψφL : ψL ≫ φL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₂), ← Category.assoc, hψL,
      Category.assoc, hφL, ← Category.assoc, hψφ', Category.id_comp, Category.comp_id]
  have hφLs : φL ≫ pullback.snd B.X.hom (sp e₂L) = pullback.snd B.X.hom (sp e₁L) := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs, xc_snd]
  have hc : sp e₂L = sp (τ : L →+* L) ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  have hci : sp e₁L = sp (τ.symm : L →+* L) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => τ.symm_apply_apply _
  let c := xc B.X (sp (τ : L →+* L)) hc
  let cinv := xc B.X (sp (τ.symm : L →+* L)) hci
  have hcc : c ≫ cinv = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.apply_symm_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  have hcc' : cinv ≫ c = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.symm_apply_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  -- `φ_L` is a homomorphism (rigidity)
  let A₂ : PkgI3.AbVar L := G4WeilRes.bcAlong B e₂L
  let φL' : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X ⟶ A₂.X := Over.homMk φL hφLs
  haveI := specQbar_epi L
  have o1 := xc_one B.X (sp (algebraMap L Qbar)) h₁
  have o2 := xc_one B.X (sp (algebraMap L Qbar)) h₂
  have o3 : η[((G4WeilRes.conjData K B).A e₀).X].left ≫ φ₀ =
      η[((G4WeilRes.conjData K B).A e₂).X].left := by
    show (η[((G4WeilRes.conjData K B).A e₀).X] ≫ φ.hom).left = _
    rw [IsMonHom.one_hom]
  have hηL : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      η[A₂.X].left := by
    have eq : sp (algebraMap L Qbar) ≫
        η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
        sp (algebraMap L Qbar) ≫ η[A₂.X].left :=
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ φL) o1.symm).trans <|
          (Category.assoc _ _ _).trans <|
            (congrArg (η[((G4WeilRes.conjData K B).A e₀).X].left ≫ ·) hφL).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ xc B.X (sp (algebraMap L Qbar)) h₂) o3).trans o2
    exact (cancel_epi (sp (algebraMap L Qbar))).mp eq
  have hη : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X] ≫ φL' = η[A₂.X] :=
    Over.OverMorphism.ext hηL
  have hmon : IsMonHom φL' := G0FibreSimple.rigidityHom L _ _ φL' hη
  have hiso : IsIso (φL ≫ c) :=
    ⟨⟨cinv ≫ ψL, by rw [Category.assoc, reassoc_of% hcc, hφψL],
      by rw [Category.assoc, reassoc_of% hψφL, hcc']⟩⟩
  have hτ : (φL ≫ c) ≫ pullback.snd B.X.hom (sp e₁L) =
      pullback.snd B.X.hom (sp e₁L) ≫ sp (τ : L →+* L) := by
    rw [Category.assoc, xc_snd, reassoc_of% hφLs]
  have m1 : μ[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      (φL' ⊗ₘ φL').left ≫ μ[A₂.X].left :=
    congrArg Over.Hom.left (IsMonHom.mul_hom (f := φL'))
  have m2 := xc_mul B.X (sp (τ : L →+* L)) hc
  have m3 : (φL' ⊗ₘ φL').left ≫ xc2 B.X (sp (τ : L →+* L)) hc =
      pullback.map (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom (φL ≫ c) (φL ≫ c)
        (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm := by
    have f1 := xc2_fst B.X (sp (τ : L →+* L)) hc
    have f2 := Over.tensorHom_left_fst (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    have g1 := xc2_snd B.X (sp (τ : L →+* L)) hc
    have g2 := Over.tensorHom_left_snd (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans <| (congrArg _ f1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) f2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (Category.assoc _ _ _).trans <| (congrArg _ g1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) g2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨φL ≫ c, α.symm, hiso, ⟨τ, fun x => ?_, hτ, ?_, ?_⟩, fun a => ?_⟩
  · rw [← map_inv]; rfl
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) m1).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((φL' ⊗ₘ φL').left ≫ ·) m2).trans <|
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) m3)
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) hηL).trans (xc_one B.X (sp (τ : L →+* L)) hc)
  · have hmap : ∀ f₁ f₂ : B.X ⟶ B.X,
        ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ =
          φ₀ ≫ ((Over.pullback (sp (e₂ : K →+* Qbar))).map f₂).left →
        ((Over.pullback (sp e₁L)).map f₁).left ≫ φL =
          φL ≫ ((Over.pullback (sp e₂L)).map f₂).left := by
      intro f₁ f₂ h
      rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁)]
      calc xc B.X (sp (algebraMap L Qbar)) h₁ ≫ ((Over.pullback (sp e₁L)).map f₁).left ≫ φL
          = ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ ≫
              xc B.X (sp (algebraMap L Qbar)) h₂ := by
            rw [← Category.assoc, ← xc_map B.X _ h₁ f₁, Category.assoc, hφL]
        _ = φ₀ ≫ xc B.X (sp (algebraMap L Qbar)) h₂ ≫
              ((Over.pullback (sp e₂L)).map f₂).left := by
            rw [← Category.assoc, h, Category.assoc, xc_map B.X _ h₂ f₂]
        _ = _ := by rw [← Category.assoc, ← hφL, Category.assoc]
    have ht := htw (α.symm a)
    rw [RingEquiv.apply_symm_apply] at ht
    have ht' := congrArg Over.Hom.left ht
    rw [Over.comp_left, Over.comp_left] at ht'
    have key := hmap (ιB a).hom (ιB (α.symm a)).hom ht'
    change ((Over.pullback (sp e₁L)).map (ιB a).hom).left ≫ φL ≫ c =
      (φL ≫ c) ≫ ((Over.pullback (sp e₁L)).map (ιB (α.symm a)).hom).left
    rw [← Category.assoc, key, Category.assoc, xc_map B.X _ hc, Category.assoc]

/-- **`TwistDescent` holds** (kf-glue's glue Prop, statement verbatim; no hypotheses). -/
theorem twistDescent : TwistDescent := by
  intro K _ _ B ιB L _ _ hKL hHF hTw
  classical
  have key : ∀ ρ : L ≃ₐ[ℚ] L, ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ E α := by
    intro ρ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L) (E := Qbar) ρ
    exact td_construct B ιB hKL hHF hTw σ
  let G : (L ≃ₐ[ℚ] L) → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) :=
    fun ρ => if ρ = 1 then 𝟙 _ else (key ρ).choose
  let Gα : (L ≃ₐ[ℚ] L) → (O ≃+* O) :=
    fun ρ => if ρ = 1 then RingEquiv.refl O else (key ρ).choose_spec.choose
  have hG : ∀ ρ, TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
      ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ (G ρ) (Gα ρ) := by
    intro ρ
    by_cases h : ρ = 1
    · subst h
      simp only [G, Gα, if_pos rfl]
      exact twistClause_one L _ _
    · simp only [G, Gα, if_neg h]
      exact (key ρ).choose_spec.choose_spec
  let r : GQ → (L ≃ₐ[ℚ] L) := fun σ => AlgEquiv.restrictNormalHom L (act σ)
  have hr : ∀ k ∈ GQL L, r k = 1 := by
    intro k hk
    ext x
    show ((AlgEquiv.restrictNormalHom L (act k) x : L) : Qbar) = (x : Qbar)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact mem_GQL.mp hk x x.2
  refine ⟨fun σ => G (r σ), fun σ => Gα (r σ), fun σ => ?_⟩
  obtain ⟨h1, ⟨τ, hτ, hrest⟩, h3⟩ := hG (r σ)
  refine ⟨h1, ⟨τ, fun x => ?_, hrest⟩, h3, fun k hk => ?_⟩
  · rw [hτ x, ← map_inv, AlgEquiv.restrictNormalHom_apply]
    rfl
  · have e1 : r (σ * k) = r σ := by
      show AlgEquiv.restrictNormalHom L (act σ * act k) = _
      rw [map_mul]
      exact (congrArg (r σ * ·) (hr k hk)).trans (mul_one _)
    have e2 : r (k * σ) = r σ := by
      show AlgEquiv.restrictNormalHom L (act k * act σ) = _
      rw [map_mul]
      exact (congrArg (· * r σ) (hr k hk)).trans (one_mul _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show G (r k) = 𝟙 _
      rw [hr k hk]; exact if_pos rfl
    · show Gα (r k) = RingEquiv.refl O
      rw [hr k hk]; exact if_pos rfl
    · show G (r (σ * k)) = G (r σ); rw [e1]
    · show G (r (k * σ)) = G (r σ); rw [e2]
    · show Gα (r (σ * k)) = Gα (r σ); rw [e1]
    · show Gα (r (k * σ)) = Gα (r σ); rw [e2]

end G0ModField.KernelField

end TwistDescentMain

/-! # twist-descent, part FINAL: consequences (kf-glue's reductions with `TwistDescent` discharged) -/

section TwistDescentFinal

namespace G0ModField.KernelField

/-- **`ConjIsogMaps` from `MulIsogeny` alone** (kf-glue's `conjIsogMaps_of_descent` with
`twistDescent`). -/
theorem conjIsogMaps_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ConjIsogMaps :=
  conjIsogMaps_of_descent hMul twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` alone.** -/
theorem conjIsogMaps_of_kerUnitOpen' (hK : MulRigidity.KerUnitOpen) : ConjIsogMaps :=
  conjIsogMaps_of_kerUnitOpen hK twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's two cotangent glue statements alone.** -/
theorem conjIsogMaps_of_cotangent' (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ConjIsogMaps :=
  conjIsogMaps_of_cotangent h1 h2 twistDescent

/-- **`KernelFieldExists` without `TwistDescent`.** Leaves: T6, NOS, Raynaud, TorsionStructure,
T27, `KerUnitOpen`; glue: FS5 `FibreComTrivial`. -/
theorem kernelFieldExists_of_kerUnitOpen' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) :
    KernelFieldExists :=
  kernelFieldExists_of_kerUnitOpen hHFF hNOS hRay hTors t27 h5 hK twistDescent

/-- **`KernelFieldExists` without `TwistDescent`**, with `MulIsogeny`. -/
theorem kernelFieldExists_of_mulIsogeny (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny) :
    KernelFieldExists :=
  kernelFieldExists_of_descent hHFF hNOS hRay hTors t27 h5 hMul twistDescent

end G0ModField.KernelField

end TwistDescentFinal

#print axioms TwistDescentGD.exists_open_gal
#print axioms TwistDescentGD.descend
#print axioms TwistDescentXC.xc_mul
#print axioms TwistDescentXC.xc_one
#print axioms TwistDescentHFD.hfd
#print axioms G0ModField.KernelField.td_hom_inv
#print axioms G0ModField.KernelField.td_construct
#print axioms G0ModField.KernelField.twistDescent
#print axioms G0ModField.KernelField.conjIsogMaps_of_mulIsogeny
#print axioms G0ModField.KernelField.conjIsogMaps_of_kerUnitOpen'
#print axioms G0ModField.KernelField.conjIsogMaps_of_cotangent'
#print axioms G0ModField.KernelField.kernelFieldExists_of_kerUnitOpen'
#print axioms G0ModField.KernelField.kernelFieldExists_of_mulIsogeny
