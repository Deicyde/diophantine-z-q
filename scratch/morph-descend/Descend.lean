import Mathlib
import ZInQKernel.HDecomp.Objects

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

#print axioms MorphDescend.exists_descend
#print axioms MorphDescend.morphismsDescend
