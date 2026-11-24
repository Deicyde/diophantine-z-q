import ZInQKernel.Contrib.RC53Assist.AbelianCurve.FunctionField
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# The identity point and its rational place

The identity is an actual section of the structure morphism of a group scheme.
Its residue field is the ground field. When its local ring is a discrete
valuation ring, the normalized adic valuation gives a place of degree one.
The last condition is obtained for smooth integral curves in `SmoothCurve.lean`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- DEFINITION. The identity section of the actual group object.
Locator: `ZInQKernel/HDecomp/Objects.lean`, `PkgI3.AbVar.grp`;
Mathlib's `MonObj.one`, written `η[G]`. -/
def identitySection (G : Over (Spec (.of ℚ))) [GrpObj G] : Spec (.of ℚ) ⟶ G.left :=
  (η[G]).left

/-- THEOREM (proved). The identity section is a rational point over the specified base.
Locator: Mathlib's over-category equation `Over.w` for `η[G]`. -/
theorem identitySection_comp (G : Over (Spec (.of ℚ))) [GrpObj G] :
    identitySection G ≫ G.hom = 𝟙 _ := by
  exact (η[G]).w

/-- DEFINITION. The underlying identity point, the image of the sole point of the spectrum
of the rationals. Locator: `identitySection` above; Milne, cited 2008 notes, I, §1. -/
def identityPoint (G : Over (Spec (.of ℚ))) [GrpObj G] : G.left :=
  identitySection G (IsLocalRing.closedPoint ℚ)

/-- THEOREM (proved). The identity is a closed point.
Locator: `ZInQKernel/Contrib/Dim/SmoothStalk.lean`, `isClosed_singleton_of_section`;
Mathlib, `isClosedImmersion_of_comp_eq_id`. -/
theorem identityPoint_closed (G : Over (Spec (.of ℚ))) [GrpObj G] :
    IsClosed ({identityPoint G} : Set G.left) := by
  haveI := isClosedImmersion_of_comp_eq_id (Y := Spec (.of ℚ)) G.hom (identitySection G)
    (identitySection_comp G)
  have hr : Set.range (identitySection G) = {identityPoint G} := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact congrArg (identitySection G) (Subsingleton.elim p (IsLocalRing.closedPoint ℚ))
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint ℚ, rfl⟩
  rw [← hr]
  exact (identitySection G).isClosedEmbedding.isClosed_range

/-- DEFINITION. The identity point induces evaluation of its residue field in the rationals.
Locator: Mathlib, `Scheme.stalkClosedPointTo` and `Scheme.descResidueField`;
`Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField`. -/
def identityResidueToRat (G : Over (Spec (.of ℚ))) [GrpObj G] :
    G.left.residueField (identityPoint G) →+* ℚ :=
  (Scheme.descResidueField (Scheme.stalkClosedPointTo (identitySection G))).hom

/-- THEOREM (proved). A rational algebra admitting a field homomorphism back to the rationals
has no elements beyond the rationals. Locator: Mathlib, `RingHom.ext_rat` and injectivity
of homomorphisms out of a field. -/
theorem rat_algebraMap_bijective_of_hom_to_rat {F : Type} [Field F] [Algebra ℚ F]
    (φ : F →+* ℚ) : Function.Bijective (algebraMap ℚ F) := by
  refine ⟨(algebraMap ℚ F).injective, fun x => ⟨φ x, φ.injective ?_⟩⟩
  exact RingHom.congr_fun (RingHom.ext_rat (φ.comp (algebraMap ℚ F)) (RingHom.id ℚ)) (φ x)

/-- THEOREM (proved). The residue field of a rational point has dimension one over the
rationals, for any rational algebra structure.
Locator: `rat_algebraMap_bijective_of_hom_to_rat`; Mathlib, `AlgEquiv.ofBijective`. -/
theorem finrank_eq_one_of_hom_to_rat {F : Type} [Field F] [Algebra ℚ F] (φ : F →+* ℚ) :
    Module.finrank ℚ F = 1 := by
  let e : ℚ ≃ₐ[ℚ] F :=
    AlgEquiv.ofBijective (Algebra.ofId ℚ F) (rat_algebraMap_bijective_of_hom_to_rat φ)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- DEFINITION. The constants act on the local ring by pulling back and taking a germ.
Locator: `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`,
`Scheme.baseRingToStalk`. -/
@[instance_reducible]
def stalkAlgebra {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).toAlgebra

/-- THEOREM (proved). Constants, the local ring, and the function field form a scalar tower.
Locator: `TauCeti/AlgebraicGeometry/Scheme/BaseAlgebra.lean`,
`Scheme.baseStalkFunctionFieldIsScalarTower`. -/
theorem stalk_functionField_tower {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f x
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f x
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change X.germToFunctionField ⊤ (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) c) =
    algebraMap (X.presheaf.stalk x) X.functionField
      (X.presheaf.germ ⊤ x trivial (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) c))
  exact (X.algebraMap_germ_eq_germToFunctionField (U := ⊤) (x := x) trivial _).symm

/-- DEFINITION. The place given by the normalized valuation of the identity's discrete local
ring. This is a construction from the local ring, not a chosen arbitrary rational place.
Locator: `TauCeti.Place.ofPrime`; the maximal ideal in
`IsDiscreteValuationRing.maximalIdeal`. -/
def identityPlace (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    TauCeti.Place ℚ G.left.functionField := by
  letI := functionFieldAlgebra G.hom
  letI := stalkAlgebra G.hom (identityPoint G)
  haveI := stalk_functionField_tower G.hom (identityPoint G)
  exact TauCeti.Place.ofPrime ℚ G.left.functionField
    (IsDiscreteValuationRing.maximalIdeal (G.left.presheaf.stalk (identityPoint G)))

/-- THEOREM (proved). The place constructed from the identity has degree one.
Locator: `TauCeti.Place.degree_ofPrime`; the residue-field evaluation at the identity,
`identityResidueToRat`, and `finrank_eq_one_of_hom_to_rat`. -/
theorem identityPlace_degree (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G))] :
    letI := functionFieldAlgebra G.hom
    (identityPlace G).degree = 1 := by
  letI := functionFieldAlgebra G.hom
  letI := stalkAlgebra G.hom (identityPoint G)
  haveI := stalk_functionField_tower G.hom (identityPoint G)
  rw [identityPlace, TauCeti.Place.degree_ofPrime]
  exact finrank_eq_one_of_hom_to_rat
    (F := IsLocalRing.ResidueField (G.left.presheaf.stalk (identityPoint G)))
    (identityResidueToRat G)

/-- THEOREM (proved). The valuation ring of the identity place is exactly the image of the
identity's local ring in the function field.
Locator: `TauCeti.Place.integers_ofPrime`;
Mathlib, `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`. -/
theorem identityPlace_integers (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
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

end ZInQ.Contrib.RC53Assist.AbelianCurve
