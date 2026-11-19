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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat.lean
  Source sha256  : 98aa68017fe715fbde6457c8771027c964f767b5423d8ad02a0606ac5ebf7414
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
r2nos_open_dual "CategoryTheory AlgebraicGeometry TensorProduct"

namespace P2mTensorExact
r2nos_namespace_dual

open AlgebraicGeometry.OModulePresheaf
r2nos_open_dual "AlgebraicGeometry.OModulePresheaf"

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (G : OModulePresheaf π)

noncomputable def appT {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) :
    (F.tensor G).obj U.1 →ₗ[R] (F'.tensor G).obj U.1 where
  toFun t := show (F'.tensor G).obj U.1 from
    (φ.appSections U).rTensor (G.obj U.1) (show F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1 from t)
  map_add' s t := map_add ((φ.appSections U).rTensor (G.obj U.1)) s t
  map_smul' r t := map_smul ((φ.appSections U).rTensor (G.obj U.1))
    ((Scheme.TwoAffineOpenCover.algebraOfHom π U.1).algebraMap r) t

theorem appT_apply {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens)
    (t : F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1) :
    appT G φ U (show (F.tensor G).obj U.1 from t) =
      (show (F'.tensor G).obj U.1 from (φ.appSections U).rTensor (G.obj U.1) t) := rfl

theorem appT_tmul {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) (x : F.obj U.1) (y : G.obj U.1) :
    appT G φ U (show (F.tensor G).obj U.1 from x ⊗ₜ y) = (show (F'.tensor G).obj U.1 from φ.app U x ⊗ₜ y) := rfl

noncomputable def rTensorAffHom {F F' : OModulePresheaf π} (φ : AffHom F F') : AffHom (F.tensor G) (F'.tensor G) where
  app U := appT G φ U
  app_smul U a t := map_smul ((φ.appSections U).rTensor (G.obj U.1)) a t
  naturality {U U'} h := by
    refine LinearMap.ext fun t => ?_
    show (φ.appSections U).rTensor (G.obj U.1) (F.tensorResₛₗ G h t) =
      F'.tensorResₛₗ G h ((φ.appSections U').rTensor (G.obj U'.1) t)
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
      rw [tensorResₛₗ_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, tensorResₛₗ_tmul,
        AffHom.appSections_apply, AffHom.appSections_apply, φ.naturality_apply h]
    | add s t hs ht => simp only [map_add, hs, ht]

theorem rTensorAffHom_app {F F' : OModulePresheaf π} (φ : AffHom F F') (U : V.affineOpens) :
    (rTensorAffHom G φ).app U = appT G φ U := rfl

variable {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃)
  (hG : ∀ U : V.affineOpens, Module.Flat Γ(V, U.1) (G.obj U.1))

theorem exact_appSections (U : V.affineOpens) : Function.Exact (S.inc.appSections U) (S.proj.appSections U) := by
  have h : Function.Exact (S.inc.app U) (S.proj.app U) := LinearMap.exact_iff.mpr (S.exact U).symm
  exact h

noncomputable def affSES : AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G) where
  inc := rTensorAffHom G S.inc
  proj := rTensorAffHom G S.proj
  injective U := by
    haveI := hG U
    exact Module.Flat.rTensor_preserves_injective_linearMap (S.inc.appSections U) (S.injective U)
  surjective U := LinearMap.rTensor_surjective (G.obj U.1) (S.surjective U)
  exact U := by
    haveI := hG U
    have h := Module.Flat.rTensor_exact (G.obj U.1) (exact_appSections S U)
    have h' : Function.Exact ((rTensorAffHom G S.inc).app U) ((rTensorAffHom G S.proj).app U) := h
    exact (LinearMap.exact_iff.mp h').symm

include hG in
theorem main :
    ∃ S' : AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G),
      ∀ U : V.affineOpens,
        (∀ (x : F₁.obj U.1) (y : G.obj U.1),
          S'.inc.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₂.tensor G).obj U.1 from S.inc.app U x ⊗ₜ[Γ(V, U.1)] y)) ∧
        (∀ (x : F₂.obj U.1) (y : G.obj U.1),
          S'.proj.app U (show (F₂.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₃.tensor G).obj U.1 from S.proj.app U x ⊗ₜ[Γ(V, U.1)] y)) :=
  ⟨affSES G S hG, fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩

end P2mTensorExact

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (G : OModulePresheaf π)
    (hG : ∀ U : V.affineOpens, Module.Flat Γ(V, U.1) (G.obj U.1)) :
    ∃ S' : OModulePresheaf.AffSES (F₁.tensor G) (F₂.tensor G) (F₃.tensor G),
      ∀ U : V.affineOpens,
        (∀ (x : F₁.obj U.1) (y : G.obj U.1),
          S'.inc.app U (show (F₁.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₂.tensor G).obj U.1 from S.inc.app U x ⊗ₜ[Γ(V, U.1)] y)) ∧
        (∀ (x : F₂.obj U.1) (y : G.obj U.1),
          S'.proj.app U (show (F₂.tensor G).obj U.1 from x ⊗ₜ[Γ(V, U.1)] y) =
            (show (F₃.tensor G).obj U.1 from S.proj.app U x ⊗ₜ[Γ(V, U.1)] y)) :=
  P2mTensorExact.main G S hG
end S_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
