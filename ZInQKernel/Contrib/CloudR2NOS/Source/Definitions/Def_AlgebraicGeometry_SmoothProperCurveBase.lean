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
  Source file    : Definitions/Def_AlgebraicGeometry_SmoothProperCurveBase.lean
  Source sha256  : 02af7bf931f10dd04d87b313125eaea9712ca2adb84c8f498272500b092aa68a
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
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra
r2nos_open_dual "CategoryTheory CategoryTheory.Limits NeronModelInfra"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual

instance SmoothOfRelativeDimension.smooth_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

instance SmoothOfRelativeDimension.pullback_snd (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.pullback_fst (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.fiberToSpecResidueField (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (s : S) : SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

instance IsProper.fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance

namespace SmoothProperCurve
r2nos_namespace_dual

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

abbrev specMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

abbrev baseChange : pullback c (specMap R T) ⟶ Spec (CommRingCat.of T) :=
  pullback.snd c (specMap R T)

example [SmoothOfRelativeDimension 1 c] : SmoothOfRelativeDimension 1 (baseChange R c T) :=
  inferInstance
example [IsProper c] : IsProper (baseChange R c T) := inferInstance
example [GeometricallyIntegral c] : GeometricallyIntegral (baseChange R c T) := inferInstance

variable {R c}

def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange

instance isIntegral_pullback_Spec_field [GeometricallyIntegral c] {K : Type u} [Field K]
    (ξ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) : IsIntegral (pullback c ξ) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c ξ)

example [GeometricallyIntegral c] (K : Type u) [Field K] [Algebra R K] :
    IsIntegral (pullback c (specMap R K)) := inferInstance

end SmoothProperCurve

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
