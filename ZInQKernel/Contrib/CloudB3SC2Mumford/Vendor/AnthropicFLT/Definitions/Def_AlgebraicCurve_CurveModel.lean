/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicCurve_CurveModel
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicCurve

def baseToFunctionField {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (CommRingCat.of K)) : K →+* C.functionField :=
  (C.presheaf.germ ⊤ (genericPoint C) trivial).hom.comp
    (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

structure CurveModel (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] where

  C : Scheme.{u}

  toBase : C ⟶ Spec (CommRingCat.of K)

  [isIntegral : IsIntegral C]

  [isProper : IsProper toBase]

  [smooth : SmoothOfRelativeDimension 1 toBase]

  ffEquiv : L ≃+* C.functionField

  ffEquiv_algebraMap : ∀ a : K, ffEquiv (algebraMap K L a) = baseToFunctionField toBase a

  placeOfPoint : closedPoints C → Place K L

  placeOfPoint_bijective : Function.Bijective placeOfPoint

  range_stalk_eq : ∀ x : closedPoints C,
    ((ffEquiv.symm : C.functionField ≃+* L).toRingHom.comp
        (algebraMap (C.presheaf.stalk x.1) C.functionField)).range =
      (placeOfPoint x).toValuationSubring.toSubring

  finset_subset_affineOpen : ∀ F : Finset C, ∃ U : C.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U

attribute [instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

namespace CurveModel

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

abbrev functionFieldAlgebra (M : CurveModel K L) : Algebra K M.C.functionField :=
  (baseToFunctionField M.toBase).toAlgebra

def ffAlgEquiv (M : CurveModel K L) :
    letI := M.functionFieldAlgebra
    L ≃ₐ[K] M.C.functionField :=
  letI := M.functionFieldAlgebra
  AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap

theorem ffAlgEquiv_apply (M : CurveModel K L) (f : L) : M.ffAlgEquiv f = M.ffEquiv f := rfl

def placeEquiv (M : CurveModel K L) : closedPoints M.C ≃ Place K L :=
  Equiv.ofBijective M.placeOfPoint M.placeOfPoint_bijective

theorem placeEquiv_apply (M : CurveModel K L) (x : closedPoints M.C) :
    M.placeEquiv x = M.placeOfPoint x := rfl

def pointEquivPlace [IsAlgClosed K] (M : CurveModel K L) :
    {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _} ≃ Place K L :=
  (pointEquivClosedPoint M.toBase).trans M.placeEquiv

theorem pointEquivPlace_apply [IsAlgClosed K] (M : CurveModel K L)
    (p : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}) :
    M.pointEquivPlace p = M.placeOfPoint (pointEquivClosedPoint M.toBase p) := rfl

end CurveModel

end AlgebraicCurve

end
