/-! ## g0-assemble2: kernel-field, assembled as in scratch/kernel-field/assemble.sh: morph-descend Descend.lean
3-401, inertia-homs InertiaHoms.lean 7-2089 (= g4-weilres G4.lean + inertia-homs), morph-descend G4Closed.lean
1867-1897, kernel-field New.lean (its Part 4, g0-dim's Dim.lean 107-305, is part 10; its Part 5 is part 75) -/
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

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField
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

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q CategoryTheory AlgebraicGeometry Limits MonObj PkgI3 PkgI3.AbVar InertiaHoms

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

section PartClosed
namespace G4WeilRes

/-- **`MorphismsDescend` of G4 (EGA IV₃ 8.8.2), proved.** The statement here (over
`GlueB3Unram.Qbar`) is `MorphDescend.MorphismsDescend` (over `MorphDescend.Qbar`); both `Qbar`s
are the reducible abbreviation `AlgebraicClosure ℚ`. -/
theorem morphismsDescend : MorphismsDescend := MorphDescend.morphismsDescend

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField PkgI3 AlgebraicGeometry

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

open GlueB3Unram hiding UnramifiedAt
open GlueDescent.B2Q NumberField PkgI3 PkgI3.AbVar CategoryTheory MonObj

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

-- (g0-assemble2) section FS5Copy (verbatim copy of g0-fibresimple's `FibreComTrivial`) is not repeated: part 40 defines it.

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

-- (g0-assemble2) section FS4Copy (verbatim copies of g0-fibresimple's §1, FS4) is not repeated: part 40 defines the same text.

section EndEqOSec

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct Quaternion

namespace G0ModField.KernelField

/-- **Remaining glue 4a′ (pure algebra): `𝒪` is a maximal order of `B = (2,-3)_ℚ`.** A subring of
`B` containing `𝒪` whose elements are integral over `ℤ` is contained in `𝒪`. STANDARD (the
order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` has reduced discriminant `6 = disc B`; Vignéras,
*Arithmétique des algèbres de quaternions*, III §5, UNVERIFIED locator). A finite lattice
computation; not compiled here. -/
def OMaximal : Prop :=
  ∀ R : Subring LeafQM.B, LeafQM.O ≤ R → (∀ x ∈ R, IsIntegral ℤ x) → R ≤ LeafQM.O

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

end G0ModField.KernelField

end EndEqOSec

