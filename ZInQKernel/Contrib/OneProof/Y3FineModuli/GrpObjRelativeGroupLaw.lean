import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

/-!
# Actual group objects yield the source relative group law on affine bases

New, separately checked work after the frozen tangent-trace draft. This file
is not imported by that draft's entry and is not part of its reviewed commit.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean, lines 57–110.
Apache-2.0; original LICENSE/NOTICE/ATTRIBUTION are retained in Vendor/AnthropicFLT.
Changes: import current namespaced source definitions and isolate this port
in the Y3 Source namespace. The source's actual group-object construction body
and point-operation equations are retained. No moduli witness or R1 conclusion
is claimed. General-base restriction/gluing and target QMAbScheme action
transport remain separate work.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open scoped CategoryTheory.MonObj

/-- The source's actual pointwise relative group law induced by a group object
of schemes over an affine base. This constructs the group law; it is not a
hypothesis that a desired derivative representation already exists. -/
def relativeGroupLawOfGrpObj (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)] : RelativeGroupLaw R f where
  mul {T} t x y :=
    overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y)
  one {T} t := overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f)
  inv {T} t x := overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹
  mul_assoc {T} t x y z := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_assoc]
  one_mul {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [one_mul, overHomToSchemeHomOver_schemeHomOverToOverHom]
  mul_one {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_one, overHomToSchemeHomOver_schemeHomOverToOverHom]
  inv_mul_cancel {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    have key : ∀ z : SchemeHomOver t f,
        schemeHomOverComp ψ hψ z =
          overHomToSchemeHomOver
            ((Over.homMk ψ (by simpa using hψ) : Over.mk t' ⟶ Over.mk t) ≫
              schemeHomOverToOverHom z) := by
      intro z
      apply Subtype.ext
      simp
    rw [key, key, key]
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [MonObj.comp_mul]

@[simp]
theorem relativeGroupLawOfGrpObj_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).mul t x y =
      overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (relativeGroupLawOfGrpObj R f).one t =
      overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).inv t x =
      overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹ :=
  rfl

end ZInQ.Contrib.OneProof.Y3FineModuli.Source
