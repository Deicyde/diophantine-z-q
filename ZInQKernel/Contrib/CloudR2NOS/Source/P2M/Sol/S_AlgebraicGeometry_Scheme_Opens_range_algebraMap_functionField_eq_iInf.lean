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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf.lean
  Source sha256  : b89caa93cd4f7d29a3c311dbc1ed630c479642cd2c457e472cc2e904dd5e9a46
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_IsAffineOpen_range_algebraMap_functionField_eq_iInf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.germToFunctionField IsIntegral Scheme exists_isAffineOpen_mem_and_subset IsAffineOpen functionField_isScalarTower"
namespace EngineOpen
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

variable {X : Scheme.{u}} [IsIntegral X]

theorem germToFunctionField_map {U V : X.Opens} [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(X, U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map i.op).hom s) = (X.germToFunctionField U).hom s := by
  change (X.presheaf.map i.op ≫ X.germToFunctionField V).hom s = _
  rw [Scheme.germToFunctionField, X.presheaf.germ_res]

end AlgebraicGeometry.EngineOpen

open AlgebraicGeometry.EngineOpen in
r2nos_open_dual "AlgebraicGeometry.EngineOpen" in
theorem solution
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (algebraMap Γ(X, U) X.functionField).range =
      ⨅ (x : X) (_ : x ∈ U), (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  classical
  apply le_antisymm
  ·
    refine le_iInf₂ fun x hx => ?_
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x, hx⟩
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap Γ(X, U) (X.presheaf.stalk x) a,
      (IsScalarTower.algebraMap_apply Γ(X, U) _ X.functionField a).symm⟩
  ·
    intro f hf

    have hW : ∀ x : U, ∃ W : X.Opens, IsAffineOpen W ∧ (x : X) ∈ W ∧ (W : Set X) ⊆ U := fun x =>
      exists_isAffineOpen_mem_and_subset x.2
    choose W hWaff hxW hWU using hW
    haveI hWne : ∀ x : U, Nonempty (W x) := fun x => ⟨⟨x, hxW x⟩⟩

    have hsec : ∀ x : U, ∃ s : Γ(X, W x), (X.germToFunctionField (W x)).hom s = f := by
      intro x
      have hfx : f ∈ (algebraMap Γ(X, W x) X.functionField).range := by
        rw [(hWaff x).range_algebraMap_functionField_eq_iInf]
        refine Subring.mem_iInf.mpr fun y => Subring.mem_iInf.mpr fun hy => ?_
        exact (Subring.mem_iInf.mp ((Subring.mem_iInf.mp hf) y)) (hWU x hy)
      obtain ⟨s, hs⟩ := hfx
      exact ⟨s, hs⟩
    choose sf hsf using hsec

    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 W sf := by
      intro x y
      haveI : Nonempty ((W x ⊓ W y : X.Opens)) := by
        obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (W x).isOpen (W y).isOpen
          ⟨x, hxW x⟩ ⟨y, hxW y⟩
        exact ⟨⟨z, hz⟩⟩
      apply X.germToFunctionField_injective (W x ⊓ W y)
      change (X.germToFunctionField (W x ⊓ W y)).hom ((X.presheaf.map _).hom (sf x)) =
        (X.germToFunctionField (W x ⊓ W y)).hom ((X.presheaf.map _).hom (sf y))
      rw [germToFunctionField_map, germToFunctionField_map, hsf, hsf]

    have hcover : U ≤ iSup W := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' W U (fun x => homOfLE (hWU x)) hcover sf hcompat
    refine ⟨s, ?_⟩

    obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty U)
    let i0 : U := ⟨x, hx⟩
    have hres : (X.presheaf.map (homOfLE (hWU i0)).op).hom s = sf i0 := hs i0
    change (X.germToFunctionField U).hom s = f
    rw [← germToFunctionField_map (homOfLE (hWU i0)) s]
    exact (congrArg (fun t => (X.germToFunctionField (W i0)).hom t) hres).trans (hsf i0)
end S_AlgebraicGeometry_Scheme_Opens_range_algebraMap_functionField_eq_iInf
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
