import Mathlib

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

/-- The diagram `L ↦ L ×_K X` of schemes. -/
noncomputable def bcDiag : (Idx E₀)ᵒᵖ ⥤ Scheme :=
  (specDiag E₀ e he ⋙ Over.pullback X.hom) ⋙ Over.forget X.left

/-- `ℚ̄ ×_K X` as a cone over `bcDiag`. -/
noncomputable def bcCone : Cone (bcDiag E₀ e he X) :=
  (Over.forget X.left).mapCone ((Over.pullback X.hom).mapCone (specCone E₀ e he))

/-- `ℚ̄ ×_K X = lim (L ×_K X)`. -/
noncomputable def bcConeIsLimit [FiniteDimensional ℚ E₀] : IsLimit (bcCone E₀ e he X) := by
  haveI : IsConnected (Idx E₀)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.forget X.left)
    (isLimitOfPreserves (Over.pullback X.hom) (specConeIsLimit E₀ e he))

theorem bcDiag_obj (L : (Idx E₀)ᵒᵖ) :
    (bcDiag E₀ e he X).obj L =
      pullback (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom := rfl

theorem bcDiag_map {L L' : (Idx E₀)ᵒᵖ} (f : L ⟶ L') :
    (bcDiag E₀ e he X).map f = pullback.lift
      (pullback.fst (Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop))) X.hom ≫
        Spec.map (inclL E₀ (leOfHom f.unop)))
      (pullback.snd _ _) (by
        change (_ ≫ _) ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e he L'.unop)) = _
        rw [Category.assoc, ← Spec.map_comp, restrL_inclL, pullback.condition]) := rfl

theorem bcCone_π_app (L : (Idx E₀)ᵒᵖ) :
    (bcCone E₀ e he X).π.app L =
      pullback.lift (pullback.fst (Spec.map (CommRingCat.ofHom e)) X.hom ≫ Spec.map (toQbar E₀ L.unop))
      (pullback.snd _ _) (by
        change (_ ≫ _) ≫ Spec.map (CommRingCat.ofHom (restrL E₀ e he L.unop)) = _
        rw [Category.assoc, ← Spec.map_comp, restrL_toQbar, pullback.condition]) := rfl

end Schemes

end MorphDescend
