import ZInQKernel.Contrib.RC53Assist.AbelianCurve.IdentityPlace

/-!
# The identity point and its place over an arbitrary field

For a group object `G` over the spectrum of an arbitrary field `K`, the identity is a `K`-point
of the structure morphism, hence a closed point. Its residue field is `K`: the evaluation at the
identity is a `K`-algebra retraction of the constants, because the identity section is a section
of the structure morphism. When the local ring at the identity is a discrete valuation ring, the
normalized adic valuation gives a place of degree one.

Over the rational numbers the residue-field step used only that every ring homomorphism to `ℚ`
is `ℚ`-linear (`ZInQ.Contrib.RC53Assist.AbelianCurve.identityPlace_degree`). Here the
compatibility of the evaluation with the constants is proved from `η ≫ π = 𝟙`.

Mathematical locator: Milne, *Abelian varieties*, version 2.00 (2008), I, §1, the identity
element of a group variety; Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
§I.1, the place of a discrete valuation ring.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.S2aNumberField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.RC53Assist.AbelianCurve (functionFieldAlgebra stalkAlgebra
  stalk_functionField_tower)

variable {K : Type} [Field K]

/-- DEFINITION. The identity section of a group object over the spectrum of a field.
Locator: Mathlib's `MonObj.one`, written `η[G]`; the rational version
`AbelianCurve.identitySection`. -/
def identitySection (G : Over (Spec (.of K))) [GrpObj G] : Spec (.of K) ⟶ G.left :=
  (η[G]).left

/-- THEOREM (proved). The identity section is a section of the structure morphism.
Locator: Mathlib's over-category equation `Over.w` for `η[G]`. -/
theorem identitySection_comp (G : Over (Spec (.of K))) [GrpObj G] :
    identitySection G ≫ G.hom = 𝟙 _ := by
  exact (η[G]).w

/-- DEFINITION. The underlying identity point, the image of the sole point of `Spec K`.
Locator: `identitySection` above; Milne, cited 2008 notes, I, §1. -/
def identityPoint (G : Over (Spec (.of K))) [GrpObj G] : G.left :=
  identitySection G (IsLocalRing.closedPoint K)

/-- THEOREM (proved). The identity is a closed point.
Locator: Mathlib, `isClosedImmersion_of_comp_eq_id`; the rational version
`AbelianCurve.identityPoint_closed`. -/
theorem identityPoint_closed (G : Over (Spec (.of K))) [GrpObj G] :
    IsClosed ({identityPoint G} : Set G.left) := by
  haveI := isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) G.hom (identitySection G)
    (identitySection_comp G)
  have hr : Set.range (identitySection G) = {identityPoint G} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact congrArg (identitySection G) (Subsingleton.elim p (IsLocalRing.closedPoint K))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint K, rfl⟩
  rw [← hr]
  exact (identitySection G).isClosedEmbedding.isClosed_range

/-- DEFINITION. Evaluation at the identity, from its residue field to the ground field.
Locator: Mathlib, `Scheme.stalkClosedPointTo` and `Scheme.descResidueField`. -/
def identityResidueToBase (G : Over (Spec (.of K))) [GrpObj G] :
    G.left.residueField (identityPoint G) →+* K :=
  (Scheme.descResidueField (Scheme.stalkClosedPointTo (identitySection G))).hom

/-- THEOREM (proved). Evaluation at the identity of a pulled-back constant is that constant.
Locator: Mathlib, `Scheme.stalkClosedPointTo_comp`, `Scheme.germ_stalkClosedPointTo_Spec`
and `Scheme.Hom.germ_stalkMap_apply`; `identitySection_comp` above. -/
theorem stalkClosedPointTo_identity_constant (G : Over (Spec (.of K))) [GrpObj G] (c : K) :
    Scheme.stalkClosedPointTo (identitySection G)
      (G.left.presheaf.germ ⊤ (identityPoint G) trivial
        (G.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = c := by
  have key : ∀ g : Spec (.of K) ⟶ Spec (.of K), g = Spec.map (𝟙 _) →
      ∀ a, Scheme.stalkClosedPointTo g
        ((Spec (.of K)).presheaf.germ ⊤ (g (IsLocalRing.closedPoint K)) trivial a) =
          (Scheme.ΓSpecIso (.of K)).hom a := by
    rintro g rfl a
    exact ConcreteCategory.congr_hom
      (Scheme.germ_stalkClosedPointTo_Spec (𝟙 (CommRingCat.of K))) a
  have h1 := Scheme.Hom.germ_stalkMap_apply G.hom ⊤ (identityPoint G) trivial
    ((Scheme.ΓSpecIso (.of K)).inv c)
  have h2 := ConcreteCategory.congr_hom
    (Scheme.stalkClosedPointTo_comp (identitySection G) G.hom)
    ((Spec (.of K)).presheaf.germ ⊤ (G.hom (identityPoint G)) trivial
      ((Scheme.ΓSpecIso (.of K)).inv c))
  have h3 := key (identitySection G ≫ G.hom)
    ((identitySection_comp G).trans (Spec.map_id _).symm) ((Scheme.ΓSpecIso (.of K)).inv c)
  change Scheme.stalkClosedPointTo (identitySection G)
    (G.left.presheaf.germ (G.hom ⁻¹ᵁ ⊤) (identityPoint G) trivial
      (G.hom.app ⊤ ((Scheme.ΓSpecIso (.of K)).inv c))) = c
  rw [← h1]
  refine (h2.symm.trans h3).trans ?_
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of K)).inv_hom_id c

/-- THEOREM (proved). A `K`-algebra field with a retraction of the constants has
`K`-dimension one. Locator: Mathlib, `AlgEquiv.ofBijective`. -/
theorem finrank_eq_one_of_retraction {F : Type} [Field F] [Algebra K F] (φ : F →+* K)
    (hφ : ∀ c : K, φ (algebraMap K F c) = c) : Module.finrank K F = 1 := by
  have hbij : Function.Bijective (algebraMap K F) :=
    ⟨(algebraMap K F).injective, fun x => ⟨φ x, φ.injective (hφ (φ x))⟩⟩
  let e : K ≃ₐ[K] F := AlgEquiv.ofBijective (Algebra.ofId K F) hbij
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- THEOREM (proved). The residue field at the identity has `K`-dimension one for the
`K`-algebra structure induced by the structure morphism.
Locator: `stalkClosedPointTo_identity_constant` and `finrank_eq_one_of_retraction` above;
Mathlib, `Scheme.residue_descResidueField`. -/
theorem identity_residue_finrank (G : Over (Spec (.of K))) [GrpObj G] :
    letI := stalkAlgebra G.hom (identityPoint G)
    Module.finrank K (IsLocalRing.ResidueField (G.left.presheaf.stalk (identityPoint G))) = 1 := by
  letI := stalkAlgebra G.hom (identityPoint G)
  refine finrank_eq_one_of_retraction (identityResidueToBase G) fun c => ?_
  change Scheme.stalkClosedPointTo (identitySection G)
    (G.left.presheaf.germ ⊤ (identityPoint G) trivial
      (G.hom.appTop ((Scheme.ΓSpecIso (.of K)).inv c))) = c
  exact stalkClosedPointTo_identity_constant G c

/-- DEFINITION. The place given by the normalized valuation of the identity's discrete local
ring. Locator: `TauCeti.Place.ofPrime`; the rational version `AbelianCurve.identityPlace`. -/
def identityPlace (G : Over (Spec (.of K))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    TauCeti.Place K G.left.functionField := by
  letI := functionFieldAlgebra G.hom
  letI := stalkAlgebra G.hom (identityPoint G)
  haveI := stalk_functionField_tower G.hom (identityPoint G)
  exact TauCeti.Place.ofPrime K G.left.functionField
    (IsDiscreteValuationRing.maximalIdeal (G.left.presheaf.stalk (identityPoint G)))

/-- THEOREM (proved). The place constructed from the identity has degree one.
Locator: `TauCeti.Place.degree_ofPrime`; `identity_residue_finrank` above. -/
theorem identityPlace_degree (G : Over (Spec (.of K))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    (identityPlace G).degree = 1 := by
  letI := functionFieldAlgebra G.hom
  letI := stalkAlgebra G.hom (identityPoint G)
  haveI := stalk_functionField_tower G.hom (identityPoint G)
  rw [identityPlace, TauCeti.Place.degree_ofPrime]
  exact identity_residue_finrank G

/-- THEOREM (proved). The valuation ring of the identity place is exactly the image of the
identity's local ring in the function field.
Locator: `TauCeti.Place.integers_ofPrime`;
Mathlib, `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`. -/
theorem identityPlace_integers (G : Over (Spec (.of K))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    (identityPlace G).integers.toSubring =
      (⊤ : Subring (G.left.presheaf.stalk (identityPoint G))).map
        (algebraMap (G.left.presheaf.stalk (identityPoint G)) G.left.functionField) := by
  letI := functionFieldAlgebra G.hom
  letI := stalkAlgebra G.hom (identityPoint G)
  haveI := stalk_functionField_tower G.hom (identityPoint G)
  rw [identityPlace, TauCeti.Place.integers_ofPrime,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := G.left.presheaf.stalk (identityPoint G)) (K := G.left.functionField)).symm

end ZInQ.Contrib.RC53Assist.S2aNumberField
