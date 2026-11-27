import Mathlib.AlgebraicGeometry.Morphisms.Affine
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FreeActionQuotient
/-!
# Inputs of the free action quotient in checkable form

The quotient theorem for a finite group action asks for freeness and for each orbit
to lie in an affine open. Freeness follows from fixed-point-freeness. The orbit
condition follows when every finite set of points lies in an affine open, and that
property passes along affine morphisms, so it can be checked on a base.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Y3QuotientDescent

open AlgebraicGeometry

/-- Every finite set of points lies in a single affine open. -/
def FiniteSetsInAffines (X : Scheme.{u}) : Prop :=
  ∀ F : Set X, F.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ F ⊆ (U : Set X)

theorem finiteSetsInAffines_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    FiniteSetsInAffines X :=
  fun _ _ => ⟨⊤, isAffineOpen_top X, fun _ _ => trivial⟩

/-- The property passes along affine morphisms. -/
theorem finiteSetsInAffines_of_isAffineHom {X S : Scheme.{u}} (π : X ⟶ S) [IsAffineHom π]
    (hS : FiniteSetsInAffines S) : FiniteSetsInAffines X := by
  intro F hF
  obtain ⟨V, hV, hFV⟩ := hS ((fun x => π x) '' F) (hF.image fun x => π x)
  refine ⟨π ⁻¹ᵁ V, hV.preimage π, fun x hx => ?_⟩
  exact hFV ⟨x, hx, rfl⟩

variable {X : Scheme.{u}} {G : Type u} [Group G] (ρ : G →* Aut X)

/-- Orbits of a finite group lie in affine opens when finite sets do. -/
theorem orbit_affine_of_finiteSetsInAffines [Finite G] (hX : FiniteSetsInAffines X) :
    ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, (ρ g).asIso.hom x ∈ U := by
  intro x
  obtain ⟨U, hU, hsub⟩ :=
    hX (Set.range fun g : G => (ρ g).asIso.hom x) (Set.finite_range _)
  exact ⟨U, hU, fun g => hsub ⟨g, rfl⟩⟩

/-- A fixed-point-free action is free in the form used by the quotient theorem. -/
theorem hfree_of_fixedPointFree
    (hfix : ∀ k : G, k ≠ 1 → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ k).asIso.hom = z → IsEmpty T) :
    ∀ g h : G, g ≠ h → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ g).asIso.hom = z ≫ (ρ h).asIso.hom → IsEmpty T := by
  intro g h hgh T z hz
  have hk : g * h⁻¹ ≠ 1 := fun h1 => hgh (mul_inv_eq_one.mp h1)
  refine hfix (g * h⁻¹) hk (z ≫ (ρ h).asIso.hom) ?_
  have hmul : (ρ h).asIso.hom ≫ (ρ (g * h⁻¹)).asIso.hom = (ρ g).asIso.hom := by
    rw [← rho_mul_hom ρ, inv_mul_cancel_right]
  rw [Category.assoc, hmul]
  exact hz

/-- The quotient by a fixed-point-free finite group action on a scheme in which every
finite set of points lies in an affine open. -/
theorem exists_effectiveEpi_quotient_of_fixedPointFree [Finite G]
    (hfix : ∀ k : G, k ≠ 1 → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ k).asIso.hom = z → IsEmpty T)
    (hX : FiniteSetsInAffines X) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y), IsPullback (actS ρ) (actT X G) p p ∧
      EffectiveEpi p ∧ IsFinite p ∧ Flat p ∧ Surjective p :=
  exists_effectiveEpi_quotient_of_free_action ρ (hfree_of_fixedPointFree ρ hfix)
    (orbit_affine_of_finiteSetsInAffines ρ hX)

end Y3QuotientDescent
