import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionRelation
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ActionFinite
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientEffectiveEpi
/-!
# Quotients of schemes by free finite group actions

For a finite group acting freely on a scheme through `ρ : G →* Aut X`, with every
orbit contained in an affine open, the finite locally free quotient theorem applies
to the action relation. The quotient map is finite, flat, locally of finite
presentation and surjective, its kernel pair is the action relation with the action
first, and it is an effective epimorphism.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Y3QuotientDescent

open AlgebraicGeometry

variable {X : Scheme.{u}} {G : Type u} [Group G] (ρ : G →* Aut X)

theorem actS_ι_apply (g : G) (y : X) :
    actS ρ (Sigma.ι (fun _ : G => X) g y) = (ρ g).asIso.hom y := by
  have h : Sigma.ι (fun _ : G => X) g ≫ actS ρ = (ρ g).asIso.hom := by
    rw [actS, Sigma.ι_desc]
  have h2 := congrArg (fun f : X ⟶ X => f y) h
  exact h2

theorem actT_ι_apply (g : G) (y : X) :
    actT X G (Sigma.ι (fun _ : G => X) g y) = y := by
  have h : Sigma.ι (fun _ : G => X) g ≫ actT X G = 𝟙 X := by
    rw [actT, Sigma.ι_desc]
  have h2 := congrArg (fun f : X ⟶ X => f y) h
  exact h2

theorem inv_apply_hom_apply (g : G) (y : X) :
    (ρ g⁻¹).asIso.hom ((ρ g).asIso.hom y) = y := by
  have key : (ρ g).asIso.hom ≫ (ρ g⁻¹).asIso.hom = 𝟙 X := by
    rw [map_inv]
    exact (ρ g).asIso.hom_inv_id
  have h2 := congrArg (fun f : X ⟶ X => f y) key
  exact h2

/-- An affine open containing the orbit of `x` gives the orbit condition of the
quotient theorem: every relation point over `x` projects into it. -/
theorem haff_of_orbit
    (horb : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, (ρ g).asIso.hom x ∈ U)
    (x : X) : ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ r : actRel X G, actS ρ r = x → actT X G r ∈ U := by
  obtain ⟨U, hU, hxU⟩ := horb x
  refine ⟨U, hU, fun r hr => ?_⟩
  obtain ⟨⟨g, y⟩, rfl⟩ := (sigmaMk fun _ : G => X).surjective r
  rw [sigmaMk_mk] at hr ⊢
  rw [actS_ι_apply] at hr
  rw [actT_ι_apply]
  subst hr
  have h := hxU g⁻¹
  rwa [inv_apply_hom_apply] at h

/-- The quotient of a scheme by a free finite group action whose orbits lie in
affine opens. -/
theorem exists_quotient_of_free_action [Finite G]
    (hfree : ∀ g h : G, g ≠ h → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ g).asIso.hom = z ≫ (ρ h).asIso.hom → IsEmpty T)
    (horb : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, (ρ g).asIso.hom x ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : actS ρ ≫ p = actT X G ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (actS ρ) (actT X G) p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  haveI : IsFinite (actT X G) := isFinite_codiagT (G := G) X
  haveI : IsFinite (actS ρ) := isFinite_actS ρ
  haveI : Flat (actS ρ) := flat_actS ρ
  haveI : LocallyOfFinitePresentation (actT X G) :=
    locallyOfFinitePresentation_actT (X := X) (G := G)
  haveI : LocallyOfFinitePresentation (actS ρ) := locallyOfFinitePresentation_actS ρ
  exact ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
    (actS ρ) (actT X G) (fun a b hs ht => rel_mono ρ hfree a b hs ht) (rel_equivalence ρ)
    (haff_of_orbit ρ horb)

/-- The same quotient map is an effective epimorphism, so it can be used for
descent. -/
theorem exists_effectiveEpi_quotient_of_free_action [Finite G]
    (hfree : ∀ g h : G, g ≠ h → ∀ {T : Scheme.{u}} (z : T ⟶ X),
      z ≫ (ρ g).asIso.hom = z ≫ (ρ h).asIso.hom → IsEmpty T)
    (horb : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ g : G, (ρ g).asIso.hom x ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y), IsPullback (actS ρ) (actT X G) p p ∧
      EffectiveEpi p ∧ IsFinite p ∧ Flat p ∧ Surjective p := by
  obtain ⟨Y, p, -, h₁, h₂, -, h₄, h₅, -⟩ := exists_quotient_of_free_action ρ hfree horb
  haveI := h₁
  haveI := h₂
  haveI := h₄
  exact ⟨Y, p, h₅, effectiveEpi_of_isFinite p, h₁, h₂, h₄⟩

end Y3QuotientDescent
