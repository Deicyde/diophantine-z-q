import ToricBaseChange.NeronComparisonV001
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The comparison morphism is a homomorphism once its generic fibre is

For a strong monoidal functor `F` (here base change to the generic fibre) and a morphism
`u : Y → N` of monoid objects such that `F u` is a homomorphism and `F` is injective on morphisms
`𝟙 → N` and `Y ⊗ Y → N` (here: the Néron mapping property of `N` for the smooth schemes `S'` and
`Y ×_{S'} Y`), `u` is a homomorphism (`isMonHom_of_map`). Applied to the comparison
`u : N ×_S S' → N'` with `F u = genIso ≫ gen'⁻¹`, this reduces the homomorphism property of `u` to
that of `genIso` (`isMonHom_comparison_of_genIso`).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Functor.LaxMonoidal
open scoped CategoryTheory.Obj

namespace ToricBaseChange.Comparison

universe v₁ v₂ u₁ u₂

theorem isMonHom_of_map {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {Y N : C} [MonObj Y] [MonObj N] (u : Y ⟶ N) [IsMonHom (F.map u)]
    (inj1 : ∀ a b : 𝟙_ C ⟶ N, F.map a = F.map b → a = b)
    (inj2 : ∀ a b : Y ⊗ Y ⟶ N, F.map a = F.map b → a = b) : IsMonHom u := by
  constructor
  · apply inj1
    have h := IsMonHom.one_hom (f := F.map u)
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc] at h
    rw [Functor.map_comp]
    exact (cancel_epi (ε F)).mp h
  · apply inj2
    have h := IsMonHom.mul_hom (f := F.map u)
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, ← Category.assoc _ (Functor.LaxMonoidal.μ F N N),
      μ_natural, Category.assoc] at h
    rw [Functor.map_comp, Functor.map_comp]
    exact (cancel_epi (Functor.LaxMonoidal.μ F Y Y)).mp h

section Apply

open AlgebraicGeometry Limits

variable {S S' E E' : Scheme.{0}} (h : S' ⟶ S) (j : E ⟶ S) (j' : E' ⟶ S') (g : E' ⟶ E)
  (hsq : j' ≫ h = g ≫ j)

/-- **The comparison `u : N ×_S S' → N'` is a homomorphism** once the canonical generic-fibre
identification `genIso` is one (the generic fibre of `u` is `genIso ≫ gen'⁻¹`; injectivity on
`𝟙` and `Y ⊗ Y` comes from the Néron mapping property of `N'`). -/
theorem isMonHom_comparison_of_genIso (N : Over S) [GrpObj N] [Smooth N.hom] (AX : Over E)
    [GrpObj AX] (gen : (Over.pullback j).obj N ≅ AX) (N' : Over S') [GrpObj N']
    (gen' : (Over.pullback j').obj N' ≅ (Over.pullback g).obj AX) [IsMonHom gen'.hom]
    [IsMonHom (genIso h j j' g hsq N AX gen).hom]
    (hN' : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective fun f : Y ⟶ N' => (Over.pullback j').map f ≫ gen'.hom)
    (u : bc h N ⟶ N')
    (hu : (Over.pullback j').map u ≫ gen'.hom = (genIso h j j' g hsq N AX gen).hom) :
    IsMonHom u := by
  have e : (Over.pullback j').map u = (genIso h j j' g hsq N AX gen).hom ≫ gen'.inv := by
    rw [← hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  haveI : IsMonHom ((Over.pullback j').map u) := by rw [e]; infer_instance
  have inj : ∀ (Y : Over S') [Smooth Y.hom] (a b : Y ⟶ N'),
      (Over.pullback j').map a = (Over.pullback j').map b → a = b := fun Y _ a b hab =>
    (hN' Y).1 (by simp only [hab])
  haveI : Smooth (𝟙_ (Over S')).hom := by change Smooth (𝟙 S'); infer_instance
  haveI : Smooth (bc h N ⊗ bc h N).hom := by
    change Smooth (pullback.fst (bc h N).hom (bc h N).hom ≫ (bc h N).hom); infer_instance
  exact isMonHom_of_map (Over.pullback j') u (inj _) (inj _)

end Apply

end ToricBaseChange.Comparison
