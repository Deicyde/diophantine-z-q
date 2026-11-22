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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion.lean
  Source sha256  : 0df251f7e0c37c6c32065a87ee2ff92a45519b4ccdf4076d37e6b041b744aa80
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    {X T Y S : Scheme.{u}} {π : X ⟶ T} {j : S ⟶ T} [IsOpenImmersion j] {ρ : Y ⟶ S} {u : Y ⟶ X}
    (hu : IsPullback u ρ π j) (F : X.Modules) :
    IsIso (Scheme.Modules.baseChangeHom hu.w F) := by

  haveI : IsOpenImmersion u := by
    rw [show u = hu.isoPullback.hom ≫ pullback.fst π j from hu.isoPullback_hom_fst.symm]
    infer_instance
  have hrange : ∀ U : T.Opens, U ≤ j.opensRange → π ⁻¹ᵁ U ≤ u.opensRange := by
    intro U hU x hx
    obtain ⟨s, hs⟩ := hU hx
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := j) x s hs.symm
    refine ⟨hu.isoPullback.inv.base z, ?_⟩
    change (hu.isoPullback.inv ≫ u).base z = x
    rw [hu.isoPullback_inv_fst]
    exact hz
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V

  suffices h : ∀ W : S.Opens, W = j ⁻¹ᵁ (j ''ᵁ V) → IsIso ((Scheme.Modules.baseChangeHom hu.w F).app W) from
    h V (j.preimage_image_eq V).symm
  intro W hW
  subst hW
  have hUle : j ''ᵁ V ≤ j.opensRange := j.image_le_opensRange V
  haveI i1 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange j _ _ hUle)
  haveI i2 : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction u).unit.app F).app (π ⁻¹ᵁ (j ''ᵁ V))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Scheme.Modules.bijective_unit_app_of_le_opensRange u F _ (hrange _ hUle))
  have key := Scheme.Modules.unit_app_app_comp_baseChangeHom_app π j ρ u hu.w F (j ''ᵁ V)
  have hc : IsIso ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ≫
        (Scheme.Modules.baseChangeHom hu.w F).app (j ⁻¹ᵁ (j ''ᵁ V))) := by
    rw [key]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ i2 ?_
    first
      | exact Functor.map_isIso _ _
      | exact @Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_op _)
  exact IsIso.of_isIso_comp_left (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
    ((Scheme.Modules.pushforward π).obj F)).app (j ''ᵁ V)) ((Scheme.Modules.baseChangeHom hu.w F).app (j ⁻¹ᵁ (j ''ᵁ V)))
end S_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isOpenImmersion
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
