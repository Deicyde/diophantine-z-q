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
  Source file    : Definitions/Def_AlgebraicGeometry_RelEffCartierDivOfPoint.lean
  Source sha256  : 580f78053cdc1d3b9013b6e9199ba400379f2c389909b1bdaae7fe25ecd5f7e9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
r2nos_open_dual "CategoryTheory CategoryTheory.Limits"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}

noncomputable def graphOver (a : T ⟶ 𝒞) (ha : a ≫ f = g) : T ⟶ pullback f g :=
  pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm)

lemma graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha = pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) := rfl

@[reassoc (attr := simp)]
lemma graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _

instance isClosedImmersion_graphOver [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsClosedImmersion (graphOver f a ha) := by
  have : IsClosedImmersion (graphOver f a ha ≫ pullback.snd f g) := by
    rw [graphOver_snd]; infer_instance
  exact .of_comp (graphOver f a ha) (pullback.snd f g)

instance isIso_ker_graphOver_subschemeIota_snd [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    IsIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g) := by
  have h : (graphOver f a ha).toImage ≫ ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)
      = 𝟙 T := by
    rw [← Category.assoc]
    change ((graphOver f a ha).toImage ≫ (graphOver f a ha).imageι) ≫ _ = _
    rw [Scheme.Hom.toImage_imageι, graphOver_snd]
  exact IsIso.of_isIso_fac_left h

noncomputable def RelEffCartierDiv.ofPoint [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    RelEffCartierDiv f 1 g where
  I := (graphOver f a ha).ker
  isFinite := inferInstance
  flat := inferInstance
  locallyOfFinitePresentation := inferInstance
  finrank_eq t := by
    rw [Scheme.Hom.finrank_eq_one_of_isIso ((graphOver f a ha).ker.subschemeι ≫ pullback.snd f g)]
    rfl

@[simp] lemma RelEffCartierDiv.ofPoint_I [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (graphOver f a ha).ker := rfl

variable {f} in

instance RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one (D : RelEffCartierDiv f 1 g) :
    IsIso (D.I.subschemeι ≫ pullback.snd f g) := by
  have := D.isFinite
  have := D.flat
  exact (Scheme.Hom.isIso_iff_finrank_eq _).mpr (funext fun t => D.finrank_eq t)

variable {f} in

noncomputable def RelEffCartierDiv.toPoint (D : RelEffCartierDiv f 1 g) : T ⟶ 𝒞 :=
  inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ pullback.fst f g

variable {f} in

@[reassoc (attr := simp)]
lemma RelEffCartierDiv.toPoint_comp (D : RelEffCartierDiv f 1 g) : D.toPoint ≫ f = g := by
  calc D.toPoint ≫ f
      = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ (pullback.fst f g ≫ f) := by
        simp only [RelEffCartierDiv.toPoint, Category.assoc]
    _ = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ (D.I.subschemeι ≫ pullback.snd f g) ≫ g := by
        rw [pullback.condition, Category.assoc]
    _ = g := by rw [IsIso.inv_hom_id_assoc]

end AlgebraicGeometry

end ZInQ.Contrib.CloudW03NeronSurj.FLT
