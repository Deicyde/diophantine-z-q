import ZInQKernel.OneProof.H.TailC
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.AbVarBC.Points
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# P0-A: endomorphisms of `A_{L̄}` are defined over a finite subextension

For a field `L`, `L̄ = AlgebraicClosure L` and an abelian variety `A/L`, every endomorphism `g` of
`A_{L̄}` lies over an endomorphism `g₀` of `A_F` for some finite subextension `L ⊆ F ⊆ L̄`, under the
comparison `descentCmp : A_{L̄} → A_F` (`end_descends_finite`).

* `L̄` is the filtered colimit of its finite subextensions (`ringCoconeIsColimit`), hence
  `Spec L̄ = lim Spec F` over `Spec L` (`specConeIsLimit`) and `A_{L̄} = lim A_F`
  (`bcConeIsLimit`), with affine transition maps and quasi-compact quasi-separated terms;
* a morphism `A_{L̄} → A_{L̄}` over `L̄` therefore factors through some `A_F` (`exists_descend`, from
  Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`, Stacks 01ZC: `A` is
  proper, hence quasi-compact and quasi-separated, and smooth, hence locally of finite
  presentation);
* the descended morphism preserves the identity section (cancel the epimorphism `Spec L̄ → Spec F`),
  so it is a homomorphism by rigidity (`G0FibreSimple.rigidityHom`).

The limit presentation is the one of `HDec.MorphDescend` (finite subextensions of `ℚ̄/ℚ`), adapted to
`L̄/L`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate.EndDescent

variable (L : Type) [Field L]

/-- The finite subextensions of `L̄/L`, ordered by inclusion. -/
abbrev Idx : Type := {F : IntermediateField L (AlgebraicClosure L) // FiniteDimensional L F}

instance : IsDirectedOrder (Idx L) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (Idx L) :=
  ⟨⟨⊥, LinearEquiv.finiteDimensional
    (IntermediateField.botEquiv L (AlgebraicClosure L)).symm.toLinearEquiv⟩⟩

/-- The diagram `F ↦ F` of rings. -/
noncomputable def ringDiag : Idx L ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `L̄` as a cocone. -/
noncomputable def ringCocone : Cocone (ringDiag L) :=
  Cocone.mk (CommRingCat.of (AlgebraicClosure L))
    { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L))
      naturality _ _ _ := rfl }

/-- `L̄ = colim F` over the finite subextensions. -/
noncomputable def ringCoconeIsColimit : IsColimit (ringCocone L) := by
  haveI : ReflectsColimit (ringDiag L) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure L)
    have hx : _root_.IsIntegral L x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional L (IntermediateField.adjoin L {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin L {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self L x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-! ### The base changes `A_F` as a cofiltered limit -/

section Schemes

/-- `L → F`. -/
noncomputable def restrL (F : Idx L) : L →+* F.1 := algebraMap L F.1

/-- The inclusion `F ⊆ F'` in `CommRingCat`. -/
noncomputable abbrev inclL {F F' : Idx L} (h : F ≤ F') :
    CommRingCat.of F.1 ⟶ CommRingCat.of F'.1 :=
  CommRingCat.ofHom (IntermediateField.inclusion h).toRingHom

/-- The inclusion `F ⊆ L̄` in `CommRingCat`. -/
noncomputable abbrev toΩ (F : Idx L) : CommRingCat.of F.1 ⟶ CommRingCat.of (AlgebraicClosure L) :=
  CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L))

theorem restrL_inclL {F F' : Idx L} (h : F ≤ F') :
    CommRingCat.ofHom (restrL L F) ≫ inclL L h = CommRingCat.ofHom (restrL L F') :=
  rfl

theorem restrL_toΩ (F : Idx L) :
    CommRingCat.ofHom (restrL L F) ≫ toΩ L F =
      CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)) :=
  rfl

theorem inclL_toΩ {F F' : Idx L} (h : F ≤ F') : inclL L h ≫ toΩ L F' = toΩ L F :=
  rfl

/-- The diagram `F ↦ (Spec F → Spec L)` in `Over (Spec L)`. -/
noncomputable def specDiag : (Idx L)ᵒᵖ ⥤ Over (Spec (CommRingCat.of L)) where
  obj F := Over.mk (Spec.map (CommRingCat.ofHom (restrL L F.unop)))
  map f := Over.homMk (Spec.map (inclL L (leOfHom f.unop))) (by
    dsimp
    rw [← Spec.map_comp, restrL_inclL])
  map_id F := by
    ext1
    show Spec.map (inclL L _) = 𝟙 _
    rw [show inclL L (leOfHom (𝟙 F).unop) = 𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    ext1
    show Spec.map (inclL L _) = Spec.map (inclL L _) ≫ Spec.map (inclL L _)
    rw [← Spec.map_comp]
    rfl

/-- `Spec L̄ → Spec L` as a cone over `specDiag`. -/
noncomputable def specCone : Cone (specDiag L) where
  pt := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))))
  π := { app F := Over.homMk (Spec.map (toΩ L F.unop)) (by
          dsimp [specDiag]
          rw [← Spec.map_comp, restrL_toΩ])
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          ext1
          show Spec.map (toΩ L _) = Spec.map (toΩ L _) ≫ Spec.map (inclL L _)
          rw [← Spec.map_comp, inclL_toΩ] }

/-- `Spec L̄ = lim Spec F` in `Over (Spec L)`. -/
noncomputable def specConeIsLimit : IsLimit (specCone L) := by
  haveI : IsConnected (Idx L)ᵒᵖ := IsCofiltered.isConnected _
  apply isLimitOfReflects (Over.forget _)
  have h := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit L).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

variable (X : Over (Spec (CommRingCat.of L)))

/-- The diagram `F ↦ F ×_L X` of schemes, as a composite of functors. -/
noncomputable def bcDiag' : (Idx L)ᵒᵖ ⥤ Scheme :=
  (specDiag L ⋙ Over.pullback X.hom) ⋙ Over.forget X.left

/-- `L̄ ×_L X` as a cone over `bcDiag'`. -/
noncomputable def bcCone' : Cone (bcDiag' L X) :=
  (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone (specCone L))

/-- `L̄ ×_L X = lim (F ×_L X)`, composite form. -/
noncomputable def bcCone'IsLimit : IsLimit (bcCone' L X) := by
  haveI : IsConnected (Idx L)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) (specConeIsLimit L))

/-- The diagram `F ↦ F ×_L X` of schemes, written with explicit pullbacks. -/
noncomputable abbrev bcDiag : (Idx L)ᵒᵖ ⥤ Scheme where
  obj F := pullback (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom
  map {F F'} f := pullback.lift
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom ≫
        Spec.map (inclL L (leOfHom f.unop)))
      (pullback.snd _ _) (by
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL, pullback.condition])
  map_id F := (bcDiag' L X).map_id F
  map_comp f g := (bcDiag' L X).map_comp f g

/-- `L̄ ×_L X` as a cone over `bcDiag`, written with explicit pullbacks. -/
noncomputable abbrev bcCone : Cone (bcDiag L X) where
  pt := pullback (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) X.hom
  π := { app F := pullback.lift
          (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) X.hom ≫
            Spec.map (toΩ L F.unop))
          (pullback.snd _ _) (by
            rw [Category.assoc, ← Spec.map_comp, restrL_toΩ, pullback.condition])
         naturality F F' f := (bcCone' L X).π.naturality f }

/-- `L̄ ×_L X = lim (F ×_L X)`. -/
noncomputable def bcConeIsLimit : IsLimit (bcCone L X) :=
  bcCone'IsLimit L X

theorem bcDiag_obj (F : (Idx L)ᵒᵖ) :
    (bcDiag L X).obj F = pullback (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom := rfl

theorem bcDiag_map_fst {F F' : (Idx L)ᵒᵖ} (f : F ⟶ F') :
    (bcDiag L X).map f ≫ pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F'.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom ≫
        Spec.map (inclL L (leOfHom f.unop)) :=
  pullback.lift_fst _ _ _

theorem bcDiag_map_snd {F F' : (Idx L)ᵒᵖ} (f : F ⟶ F') :
    (bcDiag L X).map f ≫ pullback.snd (Spec.map (CommRingCat.ofHom (restrL L F'.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom :=
  pullback.lift_snd _ _ _

theorem bcCone_π_app_fst (F : (Idx L)ᵒᵖ) :
    (bcCone L X).π.app F ≫ pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) X.hom ≫
        Spec.map (toΩ L F.unop) :=
  pullback.lift_fst _ _ _

theorem bcCone_π_app_snd (F : (Idx L)ᵒᵖ) :
    (bcCone L X).π.app F ≫ pullback.snd (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) X.hom :=
  pullback.lift_snd _ _ _

end Schemes

/-! ### Descent of morphisms -/

section Main

/-- The comparison `L̄ ×_L X → F ×_L X` (written `X ×_L L̄ → X ×_L F`). -/
noncomputable def cmp (X : Over (Spec (CommRingCat.of L))) (F : Idx L) :
    pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ⟶
      pullback X.hom (Spec.map (CommRingCat.ofHom (restrL L F))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (toΩ L F)) (by
    rw [pullback.condition, Category.assoc, ← Spec.map_comp, restrL_toΩ])

theorem bcDiag_compactSpace (X : Over (Spec (CommRingCat.of L))) [QuasiCompact X.hom]
    (F : (Idx L)ᵒᵖ) : CompactSpace ((bcDiag L X).obj F) := by
  rw [bcDiag_obj]
  infer_instance

theorem bcDiag_quasiSeparatedSpace (X : Over (Spec (CommRingCat.of L))) [QuasiSeparated X.hom]
    (F : (Idx L)ᵒᵖ) : QuasiSeparatedSpace ((bcDiag L X).obj F) := by
  rw [bcDiag_obj]
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst _ _)

theorem bcDiag_isAffineHom (X : Over (Spec (CommRingCat.of L))) {F F' : (Idx L)ᵒᵖ} (f : F ⟶ F') :
    IsAffineHom ((bcDiag L X).map f) := by
  have t := (IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom (restrL L F'.unop))) X.hom).flip
  have s : IsPullback (pullback.snd (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom)
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom) X.hom
      (Spec.map (inclL L (leOfHom f.unop)) ≫
        Spec.map (CommRingCat.ofHom (restrL L F'.unop))) := by
    rw [← Spec.map_comp, restrL_inclL]
    exact (IsPullback.of_hasPullback _ _).flip
  have hP := IsPullback.of_right (h₁₁ := (bcDiag L X).map f) (by
    rw [bcDiag_map_snd]; exact s) (bcDiag_map_fst L X f) t
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) hP.flip inferInstance

/-- **Descent of morphisms from `L̄` to a finite subextension** (EGA IV₃ 8.8.2 (i), for
`L̄ = colim F`), from Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`.
For `X` quasi-compact quasi-separated and `Y` locally of finite presentation over `L`, every
`L̄`-morphism `φ : X_{L̄} → Y_{L̄}` lies over an `F`-morphism `ψ : X_F → Y_F` for some finite `F`. -/
theorem exists_descend (X Y : Over (Spec (CommRingCat.of L)))
    [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    (φ : pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ⟶
      pullback Y.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ (F : Idx L) (ψ : pullback X.hom (Spec.map (CommRingCat.ofHom (restrL L F))) ⟶
        pullback Y.hom (Spec.map (CommRingCat.ofHom (restrL L F)))),
      ψ ≫ pullback.snd _ _ = pullback.snd _ _ ∧ φ ≫ cmp L Y F = cmp L X F ≫ ψ := by
  classical
  let D := bcDiag L X
  let c := bcCone L X
  have hc : IsLimit c := bcConeIsLimit L X
  have h1 : ∀ i, CompactSpace (D.obj i) := bcDiag_compactSpace L X
  have h2 : ∀ i, QuasiSeparatedSpace (D.obj i) := bcDiag_quasiSeparatedSpace L X
  have h3 : ∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f) := bcDiag_isAffineHom L X
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of L)) :=
    { app F := pullback.fst (Spec.map (CommRingCat.ofHom (restrL L F.unop))) X.hom ≫
        Spec.map (CommRingCat.ofHom (restrL L F.unop))
      naturality F F' f := by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL L F'.unop)))
          (bcDiag_map_fst L X f)).trans ?_
        dsimp only
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL]
        exact (Category.comp_id _).symm }
  let a : c.pt ⟶ Y.left :=
    (pullbackSymmetry _ _).hom ≫ φ ≫ pullback.fst _ _
  have ha : c.π ≫ t = (Functor.const _).map (a ≫ Y.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app, t, a, c]
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Spec.map (CommRingCat.ofHom (restrL L F.unop)))
      (bcCone_π_app_fst L X F)).trans ?_
    dsimp only
    rw [Category.assoc, ← Spec.map_comp, restrL_toΩ, Category.assoc, Category.assoc,
      pullback.condition (f := Y.hom), reassoc_of% hφ, pullbackSymmetry_hom_comp_snd_assoc]
  obtain ⟨F, g, hg1, hg2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t Y.hom c hc a ha
  refine ⟨F.unop, (pullbackSymmetry _ _).hom ≫ pullback.lift g (pullback.fst _ _) hg2, ?_, ?_⟩
  · rw [Category.assoc, pullback.lift_snd, pullbackSymmetry_hom_comp_fst]
  have key : cmp L X F.unop ≫ (pullbackSymmetry _ _).hom =
      (pullbackSymmetry _ _).inv ≫ c.π.app F := by
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

/-! ### Endomorphisms of abelian varieties -/

section End

variable {L}

/-- `Spec L̄ → Spec F → Spec L` is `Spec L̄ → Spec L`. -/
theorem specMap_tower (F : IntermediateField L (AlgebraicClosure L)) :
    Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure L))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap L F)) =
      Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The comparison `A_{L̄} → A_F` over `Spec L̄ → Spec F` (the first projection is unchanged). -/
noncomputable def descentCmp (A : _root_.PkgI3.AbVar L)
    (F : IntermediateField L (AlgebraicClosure L)) :
    (A.baseChange (AlgebraicClosure L)).X.left ⟶ (A.baseChange F).X.left :=
  pullback.lift (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))))
    (pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure L))))
    ((pullback.condition (f := A.X.hom)
        (g := Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))))).trans
      ((congrArg (pullback.snd A.X.hom
          (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ≫ ·)
        (specMap_tower F)).symm.trans (Category.assoc _ _ _).symm))

theorem descentCmp_fst (A : _root_.PkgI3.AbVar L) (F : IntermediateField L (AlgebraicClosure L)) :
    descentCmp A F ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F))) =
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) :=
  pullback.lift_fst _ _ _

theorem descentCmp_snd (A : _root_.PkgI3.AbVar L) (F : IntermediateField L (AlgebraicClosure L)) :
    descentCmp A F ≫ pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F))) =
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure L))) :=
  pullback.lift_snd _ _ _

/-- **P0-A.** Every endomorphism of `A_{L̄}` lies over an endomorphism of `A_F` for some finite
subextension `L ⊆ F ⊆ L̄`. -/
theorem end_descends_finite (A : _root_.PkgI3.AbVar L)
    (g : _root_.PkgI3.AbVar.End (A.baseChange (AlgebraicClosure L))) :
    ∃ F : IntermediateField L (AlgebraicClosure L), FiniteDimensional L F ∧
      ∃ g₀ : _root_.PkgI3.AbVar.End (A.baseChange F),
        g.hom.left ≫ descentCmp A F = descentCmp A F ≫ g₀.hom.left := by
  obtain ⟨F, ψ, hψ, hsq⟩ := exists_descend L A.X A.X g.hom.left (Over.w g.hom)
  let ψ' : (A.baseChange F.1).X ⟶ (A.baseChange F.1).X := Over.homMk ψ hψ
  have hsq' : g.hom.left ≫ descentCmp A F.1 = descentCmp A F.1 ≫ ψ'.left := hsq
  -- `Spec L̄ → Spec F`, typed between the units of the two over categories
  let s' : (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of (AlgebraicClosure L))))).left ⟶
      (MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of F.1)))).left :=
    Spec.map (CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L)))
  haveI : Epi s' := _root_.ZInQ.Contrib.AbVarBC.epi_spec_map_field _
  have hΩ : η[(A.baseChange (AlgebraicClosure L)).X].left ≫
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) =
      Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) ≫ η[A.X].left :=
    _root_.HDec.G4Conj.one_left_fst _ A.X
  have hF : η[(A.baseChange F.1).X].left ≫
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1))) =
      Spec.map (CommRingCat.ofHom (algebraMap L F.1)) ≫ η[A.X].left :=
    _root_.HDec.G4Conj.one_left_fst _ A.X
  have hΩs : η[(A.baseChange (AlgebraicClosure L)).X].left ≫
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) =
      𝟙 _ :=
    Over.w η[(A.baseChange (AlgebraicClosure L)).X]
  have hFs : η[(A.baseChange F.1).X].left ≫
      pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1))) = 𝟙 _ :=
    Over.w η[(A.baseChange F.1).X]
  have hcmpη : η[(A.baseChange (AlgebraicClosure L)).X].left ≫ descentCmp A F.1 =
      s' ≫ η[(A.baseChange F.1).X].left := by
    apply pullback.hom_ext
    · calc (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ descentCmp A F.1) ≫
            pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))
          = η[(A.baseChange (AlgebraicClosure L)).X].left ≫ (descentCmp A F.1 ≫
              pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))) :=
            Category.assoc _ _ _
        _ = η[(A.baseChange (AlgebraicClosure L)).X].left ≫
              pullback.fst A.X.hom
                (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) :=
            congrArg (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ ·) (descentCmp_fst A F.1)
        _ = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) ≫ η[A.X].left := hΩ
        _ = (s' ≫ Spec.map (CommRingCat.ofHom (algebraMap L F.1))) ≫ η[A.X].left :=
            congrArg (· ≫ η[A.X].left) (specMap_tower F.1).symm
        _ = s' ≫ (Spec.map (CommRingCat.ofHom (algebraMap L F.1)) ≫ η[A.X].left) :=
            Category.assoc _ _ _
        _ = s' ≫ (η[(A.baseChange F.1).X].left ≫
              pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))) :=
            congrArg (s' ≫ ·) hF.symm
        _ = (s' ≫ η[(A.baseChange F.1).X].left) ≫
              pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1))) :=
            (Category.assoc _ _ _).symm
    · calc (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ descentCmp A F.1) ≫
            pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))
          = η[(A.baseChange (AlgebraicClosure L)).X].left ≫ (descentCmp A F.1 ≫
              pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))) :=
            Category.assoc _ _ _
        _ = η[(A.baseChange (AlgebraicClosure L)).X].left ≫
              (pullback.snd A.X.hom
                  (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) ≫
                Spec.map (CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L)))) :=
            congrArg (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ ·) (descentCmp_snd A F.1)
        _ = (η[(A.baseChange (AlgebraicClosure L)).X].left ≫
              pullback.snd A.X.hom
                (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L))) :=
            (Category.assoc _ _ _).symm
        _ = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L))) :=
            congrArg (· ≫ Spec.map (CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure L)))) hΩs
        _ = s' := Category.id_comp _
        _ = s' ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = s' ≫ (η[(A.baseChange F.1).X].left ≫
              pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1)))) :=
            congrArg (s' ≫ ·) hFs.symm
        _ = (s' ≫ η[(A.baseChange F.1).X].left) ≫
              pullback.snd A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap L F.1))) :=
            (Category.assoc _ _ _).symm
  have hη : η[(A.baseChange F.1).X] ≫ ψ' = η[(A.baseChange F.1).X] := by
    apply Over.OverMorphism.ext
    show η[(A.baseChange F.1).X].left ≫ ψ'.left = η[(A.baseChange F.1).X].left
    apply (cancel_epi s').1
    calc s' ≫ η[(A.baseChange F.1).X].left ≫ ψ'.left
        = (s' ≫ η[(A.baseChange F.1).X].left) ≫ ψ'.left := (Category.assoc _ _ _).symm
      _ = (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ descentCmp A F.1) ≫ ψ'.left :=
          congrArg (· ≫ ψ'.left) hcmpη.symm
      _ = η[(A.baseChange (AlgebraicClosure L)).X].left ≫ (descentCmp A F.1 ≫ ψ'.left) :=
          Category.assoc _ _ _
      _ = η[(A.baseChange (AlgebraicClosure L)).X].left ≫ (g.hom.left ≫ descentCmp A F.1) :=
          congrArg (η[(A.baseChange (AlgebraicClosure L)).X].left ≫ ·) hsq'.symm
      _ = (η[(A.baseChange (AlgebraicClosure L)).X] ≫ g.hom).left ≫ descentCmp A F.1 :=
          (Category.assoc _ _ _).symm
      _ = η[(A.baseChange (AlgebraicClosure L)).X].left ≫ descentCmp A F.1 :=
          congrArg (fun t => t.left ≫ descentCmp A F.1) (IsMonHom.one_hom g.hom)
      _ = s' ≫ η[(A.baseChange F.1).X].left := hcmpη
  haveI : IsMonHom ψ' :=
    _root_.G0FibreSimple.rigidityHom F.1 (A.baseChange F.1) (A.baseChange F.1) ψ' hη
  exact ⟨F.1, F.2, _root_.PkgI3.AbVar.Hom.mk' ψ', hsq'⟩

end End

end HDec.CMSerreTate.EndDescent
