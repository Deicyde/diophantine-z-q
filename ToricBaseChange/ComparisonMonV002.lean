import ToricBaseChange.ComparisonHomV003

/-!
# The generic-fibre identification of `N ×_S S'` is a homomorphism; the comparison is one

Natural transformations between product-preserving (cartesian monoidal) functors are monoidal
(Mathlib), and the component at a monoid object of a monoidal natural transformation is a
homomorphism of the induced monoid objects (`isMonHom_app`), also when the source or the target
is an iterated base change (`isMonHom_app_comp_left`, `isMonHom_app_comp_right`). Hence `genIso`,
built from the pseudo-functoriality isomorphisms of base change and `gen`, is a homomorphism when
`gen` is (`isMonHom_genIso`), and the comparison `u : N ×_S S' → N'` is a homomorphism of group
schemes when `gen` and `gen'` are (`isMonHom_comparison`): exactly the homomorphism conditions in the
definition of a group model.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ToricBaseChange.Comparison

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} E] [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
  [CartesianMonoidalCategory E]

theorem isMonHom_app (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [NatTrans.IsMonoidal α]
    (N : C) [MonObj N] : IsMonHom (α.app N) := by
  have hu : Functor.LaxMonoidal.ε F ≫ α.app (𝟙_ C) = Functor.LaxMonoidal.ε G :=
    NatTrans.IsMonoidal.unit
  have ht : Functor.LaxMonoidal.μ F N N ≫ α.app (N ⊗ N) =
      (α.app N ⊗ₘ α.app N) ≫ Functor.LaxMonoidal.μ G N N := NatTrans.IsMonoidal.tensor N N
  constructor
  · rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, α.naturality, ← Category.assoc, hu]
  · rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, α.naturality, ← Category.assoc, ht,
      Category.assoc]

theorem isMonHom_app_comp_left (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal]
    [H.Monoidal] (α : F ⋙ G ⟶ H) [NatTrans.IsMonoidal α] (N : C) [MonObj N] :
    IsMonHom (show G.obj (F.obj N) ⟶ H.obj N from α.app N) := by
  have hu : (Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F)) ≫ α.app (𝟙_ C) =
      Functor.LaxMonoidal.ε H := NatTrans.IsMonoidal.unit (τ := α)
  have ht : (Functor.LaxMonoidal.μ G (F.obj N) (F.obj N) ≫ G.map (Functor.LaxMonoidal.μ F N N)) ≫
      α.app (N ⊗ N) = (α.app N ⊗ₘ α.app N) ≫ Functor.LaxMonoidal.μ H N N :=
    NatTrans.IsMonoidal.tensor (τ := α) N N
  have hn1 : G.map (F.map (η : 𝟙_ C ⟶ N)) ≫ α.app N = α.app (𝟙_ C) ≫ H.map η := α.naturality _
  have hn2 : G.map (F.map (μ : N ⊗ N ⟶ N)) ≫ α.app N = α.app (N ⊗ N) ≫ H.map μ := α.naturality _
  constructor
  · rw [Functor.obj.η_def, Functor.obj.η_def, Functor.obj.η_def]
    simp only [Functor.map_comp, Category.assoc, hn1]
    simp only [← Category.assoc, hu]
  · rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.obj.μ_def]
    simp only [Functor.map_comp, Category.assoc, hn2]
    simp only [← Category.assoc, ht]

theorem isMonHom_app_comp_right (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) [F.Monoidal] [G.Monoidal]
    [H.Monoidal] (β : H ⟶ F ⋙ G) [NatTrans.IsMonoidal β] (N : C) [MonObj N] :
    IsMonHom (show H.obj N ⟶ G.obj (F.obj N) from β.app N) := by
  have hu : Functor.LaxMonoidal.ε H ≫ β.app (𝟙_ C) =
      Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F) := NatTrans.IsMonoidal.unit (τ := β)
  have ht : Functor.LaxMonoidal.μ H N N ≫ β.app (N ⊗ N) = (β.app N ⊗ₘ β.app N) ≫
      (Functor.LaxMonoidal.μ G (F.obj N) (F.obj N) ≫ G.map (Functor.LaxMonoidal.μ F N N)) :=
    NatTrans.IsMonoidal.tensor (τ := β) N N
  have hn1 : H.map (η : 𝟙_ C ⟶ N) ≫ β.app N = β.app (𝟙_ C) ≫ G.map (F.map η) := β.naturality _
  have hn2 : H.map (μ : N ⊗ N ⟶ N) ≫ β.app N = β.app (N ⊗ N) ≫ G.map (F.map μ) := β.naturality _
  constructor
  · rw [Functor.obj.η_def, Functor.obj.η_def, Functor.obj.η_def]
    simp only [Functor.map_comp, Category.assoc, hn1]
    simp only [← Category.assoc, hu]
  · rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.obj.μ_def]
    simp only [Functor.map_comp, Category.assoc, hn2]
    simp only [← Category.assoc, ht]

section Apply

open AlgebraicGeometry Limits

variable {S S' E E' : Scheme.{0}} (h : S' ⟶ S) (j : E ⟶ S) (j' : E' ⟶ S') (g : E' ⟶ E)
  (hsq : j' ≫ h = g ≫ j)

/-- **`genIso` is a homomorphism** when `gen` is. -/
theorem isMonHom_genIso (N : Over S) [GrpObj N] (AX : Over E) [GrpObj AX]
    (gen : (Over.pullback j).obj N ≅ AX) [IsMonHom gen.hom] :
    IsMonHom (genIso h j j' g hsq N AX gen).hom := by
  have h1 := isMonHom_app_comp_left (Over.pullback h) (Over.pullback j') (Over.pullback (j' ≫ h))
    (Over.pullbackComp j' h).inv N
  have h2 := isMonHom_app (Over.pullback (j' ≫ h)) (Over.pullback (g ≫ j))
    (eqToIso (congrArg (fun f : E' ⟶ S => Over.pullback f) hsq)).hom N
  have h3 := isMonHom_app_comp_right (Over.pullback j) (Over.pullback g) (Over.pullback (g ≫ j))
    (Over.pullbackComp g j).hom N
  have h4 : IsMonHom ((Over.pullback g).map gen.hom) := inferInstance
  change IsMonHom ((show (Over.pullback j').obj ((Over.pullback h).obj N) ⟶
        (Over.pullback (j' ≫ h)).obj N from (Over.pullbackComp j' h).inv.app N) ≫
    (eqToIso (congrArg (fun f : E' ⟶ S => Over.pullback f) hsq)).hom.app N ≫
    (show (Over.pullback (g ≫ j)).obj N ⟶ (Over.pullback g).obj ((Over.pullback j).obj N) from
        (Over.pullbackComp g j).hom.app N) ≫ (Over.pullback g).map gen.hom)
  infer_instance

/-- **The comparison `u : N ×_S S' → N'` is a homomorphism of group schemes** when the generic
identifications `gen` and `gen'` are (the homomorphism conditions of a group model). -/
theorem isMonHom_comparison (N : Over S) [GrpObj N] [Smooth N.hom] (AX : Over E)
    [GrpObj AX] (gen : (Over.pullback j).obj N ≅ AX) [IsMonHom gen.hom] (N' : Over S') [GrpObj N']
    (gen' : (Over.pullback j').obj N' ≅ (Over.pullback g).obj AX) [IsMonHom gen'.hom]
    (hN' : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' => (Over.pullback j').map f ≫ gen'.hom)
    (u : bc h N ⟶ N')
    (hu : (Over.pullback j').map u ≫ gen'.hom = (genIso h j j' g hsq N AX gen).hom) :
    IsMonHom u := by
  haveI := isMonHom_genIso h j j' g hsq N AX gen
  exact isMonHom_comparison_of_genIso h j j' g hsq N AX gen N' gen' hN' u hu

end Apply

end ToricBaseChange.Comparison
