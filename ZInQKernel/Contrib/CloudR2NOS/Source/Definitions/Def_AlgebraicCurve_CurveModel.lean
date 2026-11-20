/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicCurve_CurveModel.lean
  Source sha256  : 56f8011498c5f3259fd2c31f83e9e487d60fb87373138483fedf297b2057d1c0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

universe u v

namespace AlgebraicCurve
r2nos_namespace_dual

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
r2nos_namespace_dual

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

end ZInQ.Contrib.CloudW03NeronSurj.FLT
