/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE and NOTICE.
Derived from Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean in
anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2.
Changes (2026-11-14): retained only the direction from a Mathlib group object
to the source's relative group law; relocated the imported definitions and
namespaces for the fixed Lean 4.35.0 H-76 port.
-/
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT
open NeronModelInfra
namespace GoodReductionJacobian

/-- The relative group law required by the source is supplied by the existing group object. -/
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
        schemeHomOverComp ψ hψ z = overHomToSchemeHomOver
          ((Over.homMk ψ (by simpa using hψ) : Over.mk t' ⟶ Over.mk t) ≫
            schemeHomOverToOverHom z) := by
      intro z
      apply Subtype.ext
      simp
    rw [key, key, key]
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [MonObj.comp_mul]

end GoodReductionJacobian
end ZInQ.Contrib.CloudW03NeronSurj.FLT
