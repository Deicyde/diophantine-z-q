import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist

/-!
# Relative Frobenius on group schemes

This adapter reuses the pinned Frobenius construction and Mathlib's cartesian
monoidal machinery. It does not construct the good-reduction or Galois data
required by C10, and does not identify a general Frobenius twist with its source.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace C10Frobenius

universe u

variable (S : Scheme.{u}) (p : ℕ) [Fact p.Prime]
  (hS : Stacks.Frobenius.IsInCharacteristic S p)

/-- The pinned relative Frobenius, bundled as a natural transformation. -/
def relativeNatTrans : 𝟭 (Over S) ⟶ frobeniusTwist S p hS where
  app := relativeFrobenius S p hS
  naturality {_ _} f := (relativeFrobenius_naturality S p hS f).symm

/-- Use the canonical monoidal structure of pullback, without changing the twist. -/
local instance twistMonoidal : (frobeniusTwist S p hS).Monoidal := by
  unfold frobeniusTwist
  infer_instance

/-- Relative Frobenius lifted to the actual group objects by upstream functoriality. -/
def relativeGroupNatTrans :
    𝟭 (Grp (Over S)) ⟶ (frobeniusTwist S p hS).mapGrp :=
  Functor.mapGrpIdIso.inv ≫ Functor.mapGrpNatTrans (relativeNatTrans S p hS)

/-- The Frobenius twist with the canonical pullback group structure. -/
abbrev groupTwist (A : Grp (Over S)) : Grp (Over S) :=
  (frobeniusTwist S p hS).mapGrp.obj A

/-- Relative Frobenius as a morphism of the original group scheme into its twist. -/
def relativeHom (A : Grp (Over S)) : A ⟶ groupTwist S p hS A :=
  (relativeGroupNatTrans S p hS).app A

/-- The packaged group map is exactly the upstream relative Frobenius on schemes. -/
@[simp] theorem relativeHom_hom (A : Grp (Over S)) :
    (relativeHom S p hS A).hom.hom = relativeFrobenius S p hS A.X := by
  change 𝟙 A.X ≫ relativeFrobenius S p hS A.X = _
  exact Category.id_comp _

/-- Relative Frobenius preserves the original group law and the canonical twisted law. -/
theorem isMonHom_relativeFrobenius (A : Grp (Over S)) :
    IsMonHom (show A.X ⟶ (groupTwist S p hS A).X
      from relativeFrobenius S p hS A.X) := by
  rw [← relativeHom_hom S p hS A]
  infer_instance

/-- The packaged relative Frobenius is natural for actual group-scheme morphisms. -/
theorem relativeHom_naturality {A B : Grp (Over S)} (f : A ⟶ B) :
    relativeHom S p hS A ≫ (frobeniusTwist S p hS).mapGrp.map f =
      f ≫ relativeHom S p hS B :=
  ((relativeGroupNatTrans S p hS).naturality f).symm

/-- On any test scheme's points, the first projection is the absolute Frobenius action. -/
theorem relativeHom_onPoints (A : Grp (Over S)) {T : Over S} (x : T ⟶ A.X) :
    (x ≫ (relativeHom S p hS A).hom.hom).left ≫
        CategoryTheory.Limits.pullback.fst A.X.hom
          (Stacks.Frobenius.absoluteFrobenius S p hS) =
      x.left ≫ Stacks.Frobenius.absoluteFrobenius A.X.left p
        (isInCharacteristic_of_hom A.X.hom p hS) := by
  rw [relativeHom_hom]
  change (x.left ≫ (relativeFrobenius S p hS A.X).left) ≫ _ = _
  rw [Category.assoc, relativeFrobenius_fst]

end C10Frobenius
