/-
H5 lane3 Step 1: constructor parts for `ReducedSubgroupOfClosedSubset` (GM3Assembly.lean).
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

PROVED here, modulo compile, from Mathlib:
* `ker_subschemeι_le_ker_of_range_subset`: for a REDUCED `W` and `g : W ⟶ X` with range inside a
  closed `Z`, `ker(ι_Z) ≤ ker g`. Here `ι_Z` is the reduced induced closed subscheme
  (`vanishingIdeal Z`).
  - Mathlib: `ker_subschemeι`, `map_bot`, `nilradical_eq_bot`, `vanishingIdeal_top`,
    `map_vanishingIdeal`, `vanishingIdeal_antimono`, `Closeds.closure_le`.
* `liftToReduced` and `liftToReduced_fac`: the induced factorization, via Mathlib
  `IsClosedImmersion.lift`/`lift_fac`.
* `range_subschemeι_vanishingIdeal`: the range of `ι_Z` is `Z`.

Remaining constructor obligations, each TRUE with an exact Prop:
* `IsReducedSubschemeVanishingIdeal`: the reduced induced subscheme is reduced; the vanishing
  ideal is radical on each affine.
* `GrpObjOfCompatibleMono`: pure category theory, in a cartesian monoidal category. Given a mono
  `j : Z ⟶ G` and maps `e, m, i` on `Z` compatible with `η, μ, ι` along `j`, `Z` carries a group
  object structure with those operations, and `j` is a monoid hom; the axioms are checked after
  composing with `j`.
* Reducedness of `Z_red ×_K Z_red`: from `GeomReducedOverAlgClosed` (C5) plus Mathlib's
  `[GeometricallyReduced f] [Flat f] [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced (pullback f g)`
  instance (Geometrically/Reduced.lean:124); any morphism to `Spec K` of a field is flat.
The constructor assembly is then:
* `e := lift η`, `m := lift ((ι_Z ⊗ ι_Z) ≫ μ)`, `i := lift (ι_Z ≫ ι)`, each range inside `Z` by
  the hypotheses;
* `GrpObjOfCompatibleMono`;
* range from `range_subschemeι_vanishingIdeal`;
* rational points lift by `liftToReduced` (`Spec K` is reduced).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Assembly

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- PROVED: the reduced induced closed subscheme receives every reduced map landing in `Z`. -/
theorem ker_subschemeι_le_ker_of_range_subset {W X : Scheme.{u}} [IsReduced W]
    (Z : Closeds X) (g : W ⟶ X) (hg : Set.range g.base ⊆ Z) :
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.ker ≤ g.ker := by
  rw [Scheme.IdealSheafData.ker_subschemeι, ← Scheme.IdealSheafData.map_bot,
    ← Scheme.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.IdealSheafData.map_vanishingIdeal]
  apply Scheme.IdealSheafData.vanishingIdeal_antimono
  rw [Closeds.closure_le]
  rintro _ ⟨w, -, rfl⟩
  exact hg ⟨w, rfl⟩

/-- The induced factorization through the reduced induced closed subscheme. -/
noncomputable def liftToReduced {W X : Scheme.{u}} [IsReduced W] (Z : Closeds X) (g : W ⟶ X)
    (hg : Set.range g.base ⊆ Z) : W ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  IsClosedImmersion.lift _ g (ker_subschemeι_le_ker_of_range_subset Z g hg)

theorem liftToReduced_fac {W X : Scheme.{u}} [IsReduced W] (Z : Closeds X) (g : W ⟶ X)
    (hg : Set.range g.base ⊆ Z) :
    liftToReduced Z g hg ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = g :=
  IsClosedImmersion.lift_fac _ _ _

theorem range_subschemeι_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.base = (Z : Set X) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- Obligation (TRUE): the reduced induced subscheme is reduced. -/
def IsReducedSubschemeVanishingIdeal : Prop :=
  ∀ {X : Scheme.{u}} (Z : Closeds X), IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-- Obligation (TRUE, pure category theory): group structure induced along a compatible mono. -/
def GrpObjOfCompatibleMono : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] [CartesianMonoidalCategory C] (G : Grp C) (Z : C)
    (j : Z ⟶ G.X) [Mono j] (e : 𝟙_ C ⟶ Z) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z),
    e ≫ j = η[G.X] → m ≫ j = (j ⊗ₘ j) ≫ μ[G.X] → i ≫ j = j ≫ ι[G.X] →
      ∃ inst : GrpObj Z, (letI := inst; IsMonHom j)

end ZInQ.Contrib.CloudR2NOS.Step1
