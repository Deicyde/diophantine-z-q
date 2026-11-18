import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The flat dimension formula at a point

For a flat local homomorphism `A → B` of local rings with `B` Noetherian,
`dim B = dim A + dim (B / 𝔪_A B)` (going down for flat maps and the height formula). For a flat
morphism of schemes `f : X → Y` with `X` locally Noetherian this gives, at every point `x`,
`dim 𝒪_{X,x} = dim 𝒪_{Y,f x} + dim (𝒪_{X,x} / 𝔪_{f x} 𝒪_{X,x})`. Applied to the quotient map
`π : U → B` of a semi-abelian identity component at the identity, the remaining input for
`dim U = dim B + t` is the dimension `t` of the closed fibre local ring.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace FlatDimension

/-- The image of the maximal ideal in a quotient of a local ring is its maximal ideal. -/
theorem map_maximalIdeal_quot {B : Type*} [CommRing B] [IsLocalRing B] (J : Ideal B)
    [IsLocalRing (B ⧸ J)] :
    (maximalIdeal B).map (Ideal.Quotient.mk J) = maximalIdeal (B ⧸ J) := by
  have h : (maximalIdeal (B ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal B :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

/-- **The flat local dimension formula** `dim B = dim A + dim (B / 𝔪_A B)`. -/
theorem ringKrullDim_eq_add_of_flat {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] :
    ringKrullDim B =
      ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) := by
  have hcomap : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap (algebraMap A B)
  have : (maximalIdeal B).LiesOver (maximalIdeal A) := ⟨hcomap.symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  set J := (maximalIdeal A).map (algebraMap A B) with hJdef
  have hJ : J ≤ maximalIdeal B := by
    rw [hJdef, Ideal.map_le_iff_le_comap, hcomap]
  have : Nontrivial (B ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hJ)
  have : IsLocalRing (B ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  rw [map_maximalIdeal_quot] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
  rfl

/-- **The flat dimension formula at a point of a scheme.** -/
theorem stalk_dim_eq_add_of_flat {X Y : Scheme} (f : X ⟶ Y) [Flat f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim (X.presheaf.stalk x ⧸
          (maximalIdeal (Y.presheaf.stalk (f x))).map
            (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x))) := by
  letI := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact ringKrullDim_eq_add_of_flat

end FlatDimension
