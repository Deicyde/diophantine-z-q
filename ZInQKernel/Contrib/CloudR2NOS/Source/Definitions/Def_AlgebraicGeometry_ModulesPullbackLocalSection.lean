/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection.lean
  Source sha256  : 3ce7de819fc1b344890d7ad7f30d8d66d9aa70ce8115517a565fa0c5ba881417
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 0 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite
r2nos_open_dual "CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

section

variable {L : Y.Modules} {U : Y.Opens}

def pullbackLocalSection (s : Γ(L, U)) : Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U) :=
  ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s

lemma pullbackLocalSection_def (s : Γ(L, U)) :
    pullbackLocalSection φ s = ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s := rfl

@[simp] lemma pullbackLocalSection_add (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s + s') = pullbackLocalSection φ s + pullbackLocalSection φ s' :=
  map_add (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

@[simp] lemma pullbackLocalSection_zero : pullbackLocalSection φ (0 : Γ(L, U)) = 0 :=
  map_zero (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom

@[simp] lemma pullbackLocalSection_neg (s : Γ(L, U)) : pullbackLocalSection φ (-s) = -pullbackLocalSection φ s :=
  map_neg (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s

@[simp] lemma pullbackLocalSection_sub (s s' : Γ(L, U)) :
    pullbackLocalSection φ (s - s') = pullbackLocalSection φ s - pullbackLocalSection φ s' :=
  map_sub (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s s'

lemma pullbackLocalSection_sum {ι : Type*} (S : Finset ι) (s : ι → Γ(L, U)) :
    pullbackLocalSection φ (∑ i ∈ S, s i) = ∑ i ∈ S, pullbackLocalSection φ (s i) :=
  map_sum (((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U).hom s S

lemma pullbackLocalSection_smul (g : Γ(Y, U)) (s : Γ(L, U)) :
    pullbackLocalSection φ (g • s) = φ.app U g • pullbackLocalSection φ s := by
  rw [pullbackLocalSection_def, Scheme.Modules.Hom.app_smul]
  rfl

lemma map_pullbackLocalSection {V : Y.Opens} (i : V ⟶ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map ((Opens.map φ.base).map i).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map i.op s) := by
  have h := (((Modules.pullbackPushforwardAdjunction φ).unit.app L).mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f :
    Γ(L, U) → Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ V))) h) s).symm

lemma map_homOfLE_pullbackLocalSection {V : Y.Opens} (hVU : V ≤ U) (s : Γ(L, U)) :
    ((Modules.pullback φ).obj L).presheaf.map
        (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hx => hVU hx)).op (pullbackLocalSection φ s) =
      pullbackLocalSection φ (L.presheaf.map (homOfLE hVU).op s) :=
  map_pullbackLocalSection φ (homOfLE hVU) s

lemma pullbackLocalSection_app {L' : Y.Modules} (θ : L ⟶ L') (s : Γ(L, U)) :
    pullbackLocalSection φ (θ.app U s) = ((Modules.pullback φ).map θ).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((Modules.pullbackPushforwardAdjunction φ).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

lemma app_pullbackLocalSection {N : X.Modules} (g : (Modules.pullback φ).obj L ⟶ N) (s : Γ(L, U)) :
    g.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N g).app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma homEquiv_symm_app_pullbackLocalSection {N : X.Modules} (k : L ⟶ (Modules.pushforward φ).obj N)
    (s : Γ(L, U)) :
    (((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).symm k).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) =
      (k.app U s : Γ(N, φ ⁻¹ᵁ U)) := by
  rw [app_pullbackLocalSection, Equiv.apply_symm_apply]

end

lemma counit_app_pullbackLocalSection {N : X.Modules} {U : Y.Opens} (n : Γ((Modules.pushforward φ).obj N, U)) :
    ((Modules.pullbackPushforwardAdjunction φ).counit.app N).app (φ ⁻¹ᵁ U) (pullbackLocalSection φ n) =
      (n : Γ(N, φ ⁻¹ᵁ U)) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U n)
    ((Modules.pullbackPushforwardAdjunction φ).right_triangle_components N)
  simp only [Functor.id_obj, Functor.comp_obj, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  exact h

theorem pullback_hom_ext {L : Y.Modules} {N : X.Modules} {g₁ g₂ : (Modules.pullback φ).obj L ⟶ N}
    (h : ∀ (U : Y.Opens) (s : Γ(L, U)),
      g₁.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s) = g₂.app (φ ⁻¹ᵁ U) (pullbackLocalSection φ s)) :
    g₁ = g₂ := by
  apply ((Modules.pullbackPushforwardAdjunction φ).homEquiv L N).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  have h₁ := app_pullbackLocalSection φ g₁ s
  have h₂ := app_pullbackLocalSection φ g₂ s
  rw [h U s] at h₁
  exact h₁.symm.trans h₂

end AlgebraicGeometry.Scheme.Modules

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
