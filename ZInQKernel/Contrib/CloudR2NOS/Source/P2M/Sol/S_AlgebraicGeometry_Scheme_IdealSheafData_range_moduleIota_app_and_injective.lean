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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective.lean
  Source sha256  : 5c81c1ffc003d2e8b889be28e02625c15c4e6b83a5c068eb642b30aaebec1820
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 4000000 in`; `set_option synthInstance.maxHeartbeats 800000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T6×1; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
r2nos_open_dual "CategoryTheory CategoryTheory.Limits"

open AlgebraicGeometry Opposite _root_.AlgebraicGeometry in
r2nos_open_dual "AlgebraicGeometry Opposite" in

theorem solution {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) ∧
      Function.Injective (I.moduleι.app U) := by

  let R := X.ringCatSheaf
  let F := I.subschemeι.unitToPushforwardUnit

  let G : SheafOfModules R ⥤ ModuleCat (R.obj.obj (op (U : X.Opens))) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op (U : X.Opens))
  haveI : G.Additive := inferInstance
  haveI : PreservesLimit (parallelPair F 0) G := inferInstance
  let e₁ : G.obj (kernel F) ≅ kernel (G.map F) := PreservesKernel.iso G F
  let e₂ : kernel (G.map F) ≅ ModuleCat.of _ (LinearMap.ker (G.map F).hom) :=
    ModuleCat.kernelIsoKer (G.map F)
  have key : G.map (kernel.ι F) =
      e₁.hom ≫ e₂.hom ≫ ModuleCat.ofHom (LinearMap.ker (G.map F).hom).subtype := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom, kernelComparison_comp_ι]

  have hfun : ⇑(I.moduleι.app U) = Subtype.val ∘ ⇑(e₁ ≪≫ e₂).toLinearEquiv := by
    funext m
    change (G.map (kernel.ι F)).hom m = _
    rw [key]
    rfl
  have hbij : Function.Bijective ⇑(e₁ ≪≫ e₂).toLinearEquiv := (e₁ ≪≫ e₂).toLinearEquiv.bijective

  have hker : ∀ s, s ∈ LinearMap.ker (G.map F).hom ↔ s ∈ (I.ideal U : Set Γ(X, U)) := fun s ↦ by
    have h1 : s ∈ LinearMap.ker (G.map F).hom ↔ (I.subschemeι.app U).hom s = 0 :=
      LinearMap.mem_ker.trans Iff.rfl
    have h2 : s ∈ (I.ideal U : Set Γ(X, U)) ↔ (I.subschemeι.app U).hom s = 0 := by
      rw [← I.ker_subschemeι_app U]
      exact RingHom.mem_ker
    exact h1.trans h2.symm
  refine ⟨?_, ?_⟩
  · rw [hfun]
    ext s
    constructor
    · rintro ⟨m, rfl⟩
      exact (hker _).mp ((e₁ ≪≫ e₂).toLinearEquiv m).2
    · intro hs
      obtain ⟨m, hm⟩ := hbij.surjective ⟨s, (hker s).mpr hs⟩
      exact ⟨m, by simp [hm]⟩
  · rw [hfun]
    exact Subtype.val_injective.comp hbij.injective
end S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
