
/-! ## §7b (local-glue). `PtFinite` proved: `K̄`-points come from finite extensions

`K̄ = colim F` over the finite subextensions `F` of `K̄/K` (as in scratch/morph-descend's
`ringCoconeIsColimit`, there for `ℚ̄`), so `Spec K̄ = lim Spec F`; since `A → Spec K` is smooth,
hence locally of finite presentation, Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC) factors every `K`-morphism `Spec K̄ → A` through some `Spec F`. -/

noncomputable section

namespace G15Ram

open CategoryTheory Limits AlgebraicGeometry

section PtFiniteSec

variable {K : Type} [Field K]

/-- The finite subextensions of `K̄/K`, ordered by inclusion. -/
abbrev FIdx (K : Type) [Field K] : Type :=
  {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K F}

instance : IsDirectedOrder (FIdx K) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (FIdx K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram `F ↦ F` of rings. -/
def fRingDiag (K : Type) [Field K] : FIdx K ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `K̄` as a cocone. -/
def fRingCocone (K : Type) [Field K] : Cocone (fRingDiag K) where
  pt := CommRingCat.of (AlgebraicClosure K)
  ι := { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure K))
         naturality _ _ _ := rfl }

/-- `K̄ = colim F` over the finite subextensions (as morph-descend's `ringCoconeIsColimit`). -/
def fRingCoconeIsColimit (K : Type) [Field K] : IsColimit (fRingCocone K) := by
  haveI : ReflectsColimit (fRingDiag K) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure K)
    have hx : _root_.IsIntegral K x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-- The diagram `F ↦ Spec F` of schemes. -/
def fSpecDiag (K : Type) [Field K] : (FIdx K)ᵒᵖ ⥤ Scheme where
  obj F := Spec (CommRingCat.of F.unop.1)
  map f := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
  map_id F := by
    rw [show CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 F).unop)).toRingHom =
      𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp]
    rfl

/-- `Spec K̄` as a cone over `fSpecDiag`. -/
def fSpecCone (K : Type) [Field K] : Cone (fSpecDiag K) where
  pt := Spec (CommRingCat.of (AlgebraicClosure K))
  π := { app F := Spec.map (CommRingCat.ofHom (algebraMap F.unop.1 (AlgebraicClosure K)))
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          change _ = _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl }

/-- `Spec K̄ = lim Spec F` (proved; `Spec` turns the colimit `fRingCoconeIsColimit` into a limit). -/
def fSpecConeIsLimit (K : Type) [Field K] : IsLimit (fSpecCone K) := by
  have h := isLimitOfPreserves Scheme.Spec (fRingCoconeIsColimit K).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

/-- **`PtFinite` holds for every abelian variety (proved).** -/
theorem ptFinite (A : PkgI3.AbVar K) : PtFinite A := by
  intro P
  have h3 : ∀ {i j : (FIdx K)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((fSpecDiag K).map f) := fun f => by
    change IsAffineHom (Spec.map _); infer_instance
  have h1 : ∀ i, CompactSpace ((fSpecDiag K).obj i) := fun i => by
    change CompactSpace (Spec _); infer_instance
  have h2 : ∀ i, QuasiSeparatedSpace ((fSpecDiag K).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _); infer_instance
  let t : fSpecDiag K ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app F := Spec.map (CommRingCat.ofHom (algebraMap K F.unop.1))
      naturality F F' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        rfl }
  have ha : (fSpecCone K).π ≫ t = (Functor.const _).map (P.left ≫ A.X.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app]
    change Spec.map _ ≫ Spec.map _ = P.left ≫ A.X.hom
    rw [← Spec.map_comp, Over.w P]
    rfl
  obtain ⟨F, g, hg, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (fSpecDiag K) t A.X.hom
      (fSpecCone K) (fSpecConeIsLimit K) P.left ha
  refine ⟨F.unop.1, F.unop.2, fun τ hτ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left =
    P.left
  rw [← hg]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact hτ x.1 x.2

/-- **`WildIter` holds for every abelian variety (proved)**: `wildIter_of_ptFinite` and
`ptFinite`. -/
theorem wildIter {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) : WildIter (p := p) A :=
  wildIter_of_ptFinite (ptFinite A)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors and the instances `RaynaudPlace`
of the leaf R6 alone (proved).** -/
theorem tateWildK_of_raynaud {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter A) hR3 hR7

end PtFiniteSec

end G15Ram

end

#print axioms G15Ram.ptFinite
#print axioms G15Ram.tateWildK_of_raynaud
