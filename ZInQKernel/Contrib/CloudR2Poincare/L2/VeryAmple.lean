import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Twist
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Pullback
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Closed restriction of very ample line bundles

H-72 round 2, lane L2. The definition below is the conventional relative
very-ampleness condition: a line bundle is the pullback of `O(1)` under a closed
immersion into finite-coordinate projective space over the given base.

The construction of a projective embedding of `J` belongs exclusively to H70 C4.
This file proves restriction and accepts that construction only as an explicit
input inside its internal AbVar-level restriction lemma. No existence fact is
assumed globally.

The twisting sheaf and pullback API are vendored from frenzymath/Jacobian-Challenge,
pin c4254cce15b3e284a0a3ae1d73936f2ee195d272 (Apache-2.0, copyright Axel Delaval,
Jie Xu, Shitan Xu). That source is not modified here.

These theorems are over arbitrary fields, hence require no algebraic closure or
extra assumptions on the characteristic-zero target.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Conventional relative very ampleness: a finite-coordinate closed embedding
with an isomorphism to the pullback of `O(1)`. This is a property of the actual
module sheaf, not a substitute for an abelian variety or a polarization. -/
def VeryAmple {X S : Scheme.{u}} (π : X ⟶ S) (L : X.Modules) : Prop :=
  ∃ (coordinates : Type u) (_ : Finite coordinates)
    (embedding : X ⟶ ℙ(coordinates; S)),
    IsClosedImmersion embedding ∧
    embedding ≫ ℙ(coordinates; S) ↘ S = π ∧
    Nonempty (L ≅ ProjectiveSpace.twistRestrict embedding 1)

/-- Every sheaf satisfying this conventional very-ampleness condition is
invertible. Invertibility is proved from `O(1)`, not assumed by the definition. -/
theorem VeryAmple.isInvertible {X S : Scheme.{u}} {π : X ⟶ S} {L : X.Modules}
    (h : VeryAmple π L) : L.IsInvertible := by
  obtain ⟨coordinates, hfinite, embedding, _, _, ⟨comparison⟩⟩ := h
  letI : Finite coordinates := hfinite
  exact SheafOfModules.IsInvertible.of_iso.{u, u, u} comparison.symm

/-- Restriction along an actual closed immersion preserves very ampleness of
line bundles, including the sheaf isomorphism to the pulled-back `O(1)`. -/
theorem VeryAmple.closedRestriction {X Y S : Scheme.{u}} {π : X ⟶ S} {L : X.Modules}
    (h : VeryAmple π L) (i : Y ⟶ X) [IsClosedImmersion i] :
    VeryAmple (i ≫ π) ((Scheme.Modules.pullback i).obj L) := by
  obtain ⟨coordinates, hfinite, embedding, hembedding, hπ, ⟨comparison⟩⟩ := h
  letI : Finite coordinates := hfinite
  letI : IsClosedImmersion embedding := hembedding
  refine ⟨coordinates, hfinite, i ≫ embedding, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hπ]
  · exact ⟨(Scheme.Modules.pullback i).mapIso comparison ≪≫
      (Scheme.Modules.pullbackComp i embedding).app
        (ProjectiveSpace.twist coordinates S 1)⟩

/-- The restriction theorem in the actual abelian-subvariety spelling of
`PolarizationRetract`. The very ample bundle on `J` is an explicit input to this
internal lemma, to be supplied by H70 C4's owned projective-embedding result. -/
theorem veryAmple_abVar_closedRestriction {k : Type} [Field k]
    (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J)
    (hi : IsClosedImmersion i.hom.left) {L : J.X.left.Modules}
    (hL : VeryAmple J.X.hom L) :
    VeryAmple B.X.hom ((Scheme.Modules.pullback i.hom.left).obj L) := by
  letI : IsClosedImmersion i.hom.left := hi
  simpa only [i.hom.w] using hL.closedRestriction i.hom.left

end ZInQ.Contrib.CloudR2Poincare.L2
