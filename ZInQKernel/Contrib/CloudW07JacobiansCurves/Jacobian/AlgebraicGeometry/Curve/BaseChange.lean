-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Curve.BaseChange), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.Basic
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.BaseChange.Field

/-!
# Extension of scalars for smooth proper curves

The pullback functor on schemes restricts to curves because properness,
geometric irreducibility, and smoothness of relative dimension one are stable
under base change.

Identity and tower comparisons lift the canonical comparisons for scheme pullback.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Curve

/-- Field extension acts on curves by the canonical scheme pullback. -/
noncomputable def baseChange (k L : Type u) [Field k] [Field L] [Algebra k L] :
    Curve k ⥤ Curve L where
  obj C := ⟨(AlgebraicGeometry.baseChange k L).obj C.carrier⟩
  map f := (AlgebraicGeometry.baseChange k L).map f
  map_id C := (AlgebraicGeometry.baseChange k L).map_id C.carrier
  map_comp f g := (AlgebraicGeometry.baseChange k L).map_comp f g

private noncomputable def idIsoOf (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) :
    baseChange baseField baseField ≅ 𝟭 (Curve baseField) :=
  NatIso.ofComponents (F := baseChange baseField baseField) (G := 𝟭 (Curve baseField))
    (fun curve ↦ isoMk (C := (baseChange baseField baseField).obj curve) (D := curve)
      (comparison.app curve.carrier))
    (fun morphism ↦ comparison.hom.naturality morphism)

private theorem idIsoOf_app (baseField : Type u) [Field baseField]
    (comparison : AlgebraicGeometry.baseChange baseField baseField ≅
      𝟭 (Over (Spec (.of baseField)))) (curve : Curve baseField) :
    (forget baseField).mapIso ((idIsoOf baseField comparison).app curve) =
      comparison.app curve.carrier := by
  apply Iso.ext
  rfl

/-- Identity field extension is naturally isomorphic to the identity on curves. -/
noncomputable def baseChange.idIso (baseField : Type u) [Field baseField] :
    baseChange baseField baseField ≅ 𝟭 (Curve baseField) :=
  idIsoOf baseField (AlgebraicGeometry.baseChange.idIso baseField)

/-- The curve identity comparison is the canonical scheme pullback comparison. -/
@[simp]
theorem forget_mapIso_baseChange_idIso_app (baseField : Type u) [Field baseField]
    (curve : Curve baseField) :
    (forget baseField).mapIso ((baseChange.idIso baseField).app curve) =
      (AlgebraicGeometry.baseChange.idIso baseField).app curve.carrier :=
  idIsoOf_app baseField _ curve

private noncomputable def compIsoOf (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField) :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  NatIso.ofComponents (F := baseChange baseField extensionField)
    (G := baseChange baseField middleField ⋙ baseChange middleField extensionField)
    (fun curve ↦ isoMk (C := (baseChange baseField extensionField).obj curve)
      (D := (baseChange baseField middleField ⋙ baseChange middleField extensionField).obj curve)
      (comparison.app curve.carrier))
    (fun morphism ↦ comparison.hom.naturality morphism)

private theorem compIsoOf_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField)
    (curve : Curve baseField) :
    (forget extensionField).mapIso
        ((compIsoOf baseField middleField extensionField comparison).app curve) =
      comparison.app curve.carrier := by
  apply Iso.ext
  rfl

private theorem compIsoOf_inv_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField]
    (comparison : AlgebraicGeometry.baseChange baseField extensionField ≅
      AlgebraicGeometry.baseChange baseField middleField ⋙
        AlgebraicGeometry.baseChange middleField extensionField)
    (curve : Curve baseField) :
    ((compIsoOf baseField middleField extensionField comparison).app curve).inv =
      (comparison.app curve.carrier).inv := rfl

/-- Direct and iterated extension of the ground field are naturally isomorphic. -/
noncomputable def baseChange.compIso (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField] :
    baseChange baseField extensionField ≅
      baseChange baseField middleField ⋙ baseChange middleField extensionField :=
  compIsoOf baseField middleField extensionField
    (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField)

/-- The curve tower comparison is the canonical scheme pullback comparison. -/
@[simp]
theorem forget_mapIso_baseChange_compIso_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (curve : Curve baseField) :
    (forget extensionField).mapIso
        ((baseChange.compIso baseField middleField extensionField).app curve) =
      (AlgebraicGeometry.baseChange.compIso baseField middleField extensionField).app
        curve.carrier :=
  compIsoOf_app baseField middleField extensionField _ curve

/-- The inverse curve tower comparison is the canonical inverse on schemes over the field. -/
@[simp]
theorem baseChange_compIso_inv_app (baseField middleField extensionField : Type u)
    [Field baseField] [Field middleField] [Field extensionField]
    [Algebra baseField middleField] [Algebra middleField extensionField]
    [Algebra baseField extensionField] [IsScalarTower baseField middleField extensionField]
    (curve : Curve baseField) :
    ((baseChange.compIso baseField middleField extensionField).app curve).inv =
      ((AlgebraicGeometry.baseChange.compIso baseField middleField extensionField).app
        curve.carrier).inv :=
  compIsoOf_inv_app baseField middleField extensionField _ curve

end AlgebraicGeometry.Curve
