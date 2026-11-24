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
  Source file    : P2M/Sol/S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.lean
  Source sha256  : 9e42f13e1ae4888ddab18a1027b26db14d6e55ade77f0436d0b260265e69ea17
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.AlgebraicGeometry Opposite TensorProduct"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pushforward tilde.adjunction moduleSpecΓFunctor Spec Spec.map Scheme pullbackSpecIso Scheme.Modules.pullbackPushforwardAdjunction tilde.functor Scheme.Modules tilde tilde.toOpen Scheme.Modules.pushforwardSpecCompΓIso tilde.pullbackSpecIso"
namespace tilde
r2nos_namespace_dual
w03_export "AlgebraicGeometry.tilde" "adjunction toOpen pullbackSpecIso"
end AlgebraicGeometry.tilde
r2nos_open_scoped "AlgebraicGeometry AlgebraicGeometry.tilde" in

theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h : ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom =
      ((((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))).ofNatIsoRight
        (Scheme.Modules.pushforwardSpecCompΓIso φ).symm).unit.app M) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h
  rw [Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)] at h
  have h2 := congrArg (· ≫ (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
    ((ModuleCat.extendScalars φ.hom ⋙ tilde.functor S).obj M)) h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h2
  exact h2

theorem solution {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by
  have h := congrArg (fun ψ => ψ.hom m) (AlgebraicGeometry.tilde.pullbackSpecIso_unit_aux φ M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Adjunction.comp_unit_app, Functor.comp_map] at h
  exact h

#print axioms solution
end S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
