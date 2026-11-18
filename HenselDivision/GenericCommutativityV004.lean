import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Commutativity of a group model from its generic fibre

Let `F : C ⥤ D` be a braided monoidal functor, `G` a monoid object of `C`, and `e : F G → A` a
homomorphism of monoid objects to a commutative monoid object `A`. If morphisms `G ⊗ G → G` are
determined by their images `F f ≫ e`, then `G` is commutative: both `μ` and `β ≫ μ` map to
`(e ⊗ e) ≫ μ_A` up to the comparison isomorphism.

Over schemes, with `F` the base change along `j : S' → S` and `e` an isomorphism of the generic fibre
with a commutative group scheme, the injectivity hypothesis is the uniqueness half of the Néron
mapping property applied to the smooth `S`-scheme `G ×_S G`. So a smooth Néron group model of an
abelian variety is commutative: commutativity is derived from the mapping property and the
commutativity of the generic fibre, not assumed.

Edition V004: qualified name of the braiding naturality lemma. Statements as in V001.
-/

open CategoryTheory MonoidalCategory Functor MonObj
open scoped Obj MonObj

namespace HenselDivision

section Generic

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D] [BraidedCategory D]

theorem isCommMonObj_of_map_injective (F : C ⥤ D) [F.Braided] {G : C}
    [MonObj G] {A : D} [MonObj A] [IsCommMonObj A] (e : F.obj G ⟶ A) [IsMonHom e]
    (hinj : Function.Injective (fun f : G ⊗ G ⟶ G => F.map f ≫ e)) : IsCommMonObj G where
  mul_comm := by
    apply hinj
    dsimp only
    have hm : LaxMonoidal.μ F G G ≫ F.map μ[G] ≫ e = (e ⊗ₘ e) ≫ μ[A] := by
      rw [← Category.assoc]
      exact IsMonHom.mul_hom e
    have key : LaxMonoidal.μ F G G ≫ F.map ((β_ G G).hom ≫ μ[G]) ≫ e =
        LaxMonoidal.μ F G G ≫ F.map μ[G] ≫ e := by
      rw [F.map_comp, Category.assoc, Functor.LaxBraided.braided_assoc, hm,
        ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]
    have := congrArg (fun h => OplaxMonoidal.δ F G G ≫ h) key
    simpa using this

end Generic

section Scheme

open AlgebraicGeometry

universe u

/-- **A Néron-type group model is commutative.** `G` a smooth group scheme over `S`, `j : S' → S`,
`e : G ×_S S' ≅ A` an isomorphism of group schemes onto a commutative group scheme over `S'`, and
morphisms from smooth `S`-schemes into `G` determined by their generic fibres. -/
theorem isCommMonObj_of_generic_injective {S S' : Scheme.{u}} (j : S' ⟶ S) (G : Over S)
    [GrpObj G] [Smooth G.hom] (A : Over S') [GrpObj A] [IsCommMonObj A]
    (e : (Over.pullback j).obj G ≅ A) [IsMonHom e.hom]
    (hN : ∀ (Y : Over S) [Smooth Y.hom],
      Function.Injective fun f : Y ⟶ G => (Over.pullback j).map f ≫ e.hom) :
    IsCommMonObj G := by
  have : Smooth (G ⊗ G).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  exact isCommMonObj_of_map_injective (Over.pullback j) e.hom (hN (G ⊗ G))

end Scheme

end HenselDivision

#check @HenselDivision.isCommMonObj_of_map_injective
#check @HenselDivision.isCommMonObj_of_generic_injective
#print axioms HenselDivision.isCommMonObj_of_map_injective
#print axioms HenselDivision.isCommMonObj_of_generic_injective
