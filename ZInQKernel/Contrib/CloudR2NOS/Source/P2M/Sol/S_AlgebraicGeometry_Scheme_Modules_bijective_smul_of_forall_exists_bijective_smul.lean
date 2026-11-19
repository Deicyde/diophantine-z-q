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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul.lean
  Source sha256  : d5a710fc0301cf5874b4423a9406ddf36541cfd8c8d08359deec023875f03239
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
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite"

namespace FrameLocalSol
r2nos_namespace_dual

variable {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤))

noncomputable abbrev res (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ

theorem res_map {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M σ W) = res M σ W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M σ W) = X.presheaf.map i.op g • res M σ W' := by
  rw [Scheme.Modules.map_smul, res_map]

noncomputable def abSheaf : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem main (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • res M σ W) :
    Function.Bijective fun g : Γ(X, V) => g • res M σ V := by
  classical
  choose U hxU hU using fun x : V => h x.1 x.2
  let W : V → X.Opens := fun x => V ⊓ U x
  have hWV : ∀ x, W x ≤ V := fun x => inf_le_left
  have hWU : ∀ x, W x ≤ U x := fun x => inf_le_right
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, ⟨hy, hxU ⟨y, hy⟩⟩⟩
  constructor
  · intro g₁ g₂ hg
    have hg' : g₁ • res M σ V = g₂ • res M σ V := hg
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf W V (fun x => homOfLE (hWV x)) hcover
    intro x
    apply (hU x (W x) (hWU x)).1
    show X.presheaf.map (homOfLE (hWV x)).op g₁ • res M σ (W x) =
      X.presheaf.map (homOfLE (hWV x)).op g₂ • res M σ (W x)
    rw [← smul_res, ← smul_res, hg']
  · intro s
    have hloc : ∀ x, ∃! g : Γ(X, W x), g • res M σ (W x) = M.presheaf.map (homOfLE (hWV x)).op s :=
      fun x => (Function.bijective_iff_existsUnique _).1 (hU x (W x) (hWU x)) _
    choose gx hgx hgx_uniq using hloc
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj W gx := by
      intro x y
      apply (hU x (W x ⊓ W y) (inf_le_left.trans (hWU x))).1
      show X.presheaf.map (Opens.infLELeft (W x) (W y)).op (gx x) • res M σ (W x ⊓ W y) =
        X.presheaf.map (Opens.infLERight (W x) (W y)).op (gx y) • res M σ (W x ⊓ W y)
      rw [← smul_res M σ (Opens.infLELeft (W x) (W y)), hgx x, ← smul_res M σ (Opens.infLERight (W x) (W y)),
        hgx y, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp]
      rfl
    obtain ⟨g, hg, -⟩ : ∃! g : Γ(X, V), ∀ x, X.presheaf.map (homOfLE (hWV x)).op g = gx x :=
      TopCat.Sheaf.existsUnique_gluing' X.sheaf W V (fun x => homOfLE (hWV x)) hcover gx hcompat
    refine ⟨g, ?_⟩
    apply TopCat.Sheaf.eq_of_locally_eq' (abSheaf M) W V (fun x => homOfLE (hWV x)) hcover
    intro x
    show M.presheaf.map (homOfLE (hWV x)).op (g • res M σ V) = M.presheaf.map (homOfLE (hWV x)).op s
    rw [smul_res, ← hgx x]
    exact congrArg (· • res M σ (W x)) (hg x)

end FrameLocalSol

theorem solution
    {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (V : X.Opens)
    (h : ∀ x ∈ V, ∃ U : X.Opens, x ∈ U ∧ ∀ W : X.Opens, W ≤ U →
      Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))) :
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op σ : Γ(M, V)) :=
  FrameLocalSol.main M σ V h
end S_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
