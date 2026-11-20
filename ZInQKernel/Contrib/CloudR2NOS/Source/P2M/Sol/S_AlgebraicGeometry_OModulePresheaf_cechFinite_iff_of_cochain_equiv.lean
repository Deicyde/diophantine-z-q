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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.lean
  Source sha256  : 011c2fc7722145a167220011fd72f101711c0910c95f5bc5bbca41cbc84e25bc
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.RingTheory.Finiteness.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme OModulePresheaf OModulePresheaf.cechFinite_iff"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "cochain d HSucc CechFinite cechFinite_iff"
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section CochainEquiv

variable {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
variable (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q)
variable (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x))

include he in
theorem d_comp_equiv (q : ℕ) :
    G.d K' q ∘ₗ (e q : F.cochain K q →ₗ[R] G.cochain K' q) = (e (q + 1) : _ →ₗ[R] _) ∘ₗ F.d K q :=
  LinearMap.ext fun x => (he q x).symm

include he in
theorem map_ker_d (q : ℕ) :
    Submodule.map (e q : F.cochain K q →ₗ[R] G.cochain K' q) (LinearMap.ker (F.d K q)) = LinearMap.ker (G.d K' q) := by
  rw [Submodule.map_equiv_eq_comap_symm, ← LinearMap.ker_comp, ← LinearEquiv.ker_comp (e (q + 1))]
  congr 1
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [he, LinearEquiv.apply_symm_apply]

def kerEquiv (q : ℕ) : LinearMap.ker (F.d K q) ≃ₗ[R] LinearMap.ker (G.d K' q) :=
  LinearEquiv.ofSubmodules (e q) _ _ (map_ker_d F G K K' e he q)

theorem kerEquiv_apply_coe (q : ℕ) (x : LinearMap.ker (F.d K q)) :
    (kerEquiv F G K K' e he q x).1 = e q x.1 := rfl

include he in
theorem map_comap_range (q : ℕ) :
    Submodule.map (kerEquiv F G K K' e he (q + 1) : _ →ₗ[R] _)
        ((LinearMap.range (F.d K q)).comap (LinearMap.ker (F.d K (q + 1))).subtype)
      = (LinearMap.range (G.d K' q)).comap (LinearMap.ker (G.d K' (q + 1))).subtype := by
  ext y
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    exact ⟨e q z, by show G.d K' q (e q z) = e (q + 1) x.1; rw [← he, hz]⟩
  · rintro ⟨z, hz⟩
    refine ⟨(kerEquiv F G K K' e he (q + 1)).symm y, ⟨(e q).symm z, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
    apply (e (q + 1)).injective
    rw [he, LinearEquiv.apply_symm_apply, hz]
    exact (congrArg Subtype.val ((kerEquiv F G K K' e he (q + 1)).apply_symm_apply y)).symm

def hSuccEquiv (q : ℕ) : F.HSucc K q ≃ₗ[R] G.HSucc K' q :=
  Submodule.Quotient.equiv _ _ (kerEquiv F G K K' e he (q + 1)) (map_comap_range F G K K' e he q)

include he in

theorem cechFinite_iff_of_cochainEquiv : F.CechFinite K ↔ G.CechFinite K' := by
  rw [OModulePresheaf.cechFinite_iff, OModulePresheaf.cechFinite_iff]
  refine ⟨fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩, fun ⟨h0, h⟩ => ⟨?_, fun q => ?_⟩⟩
  · haveI := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0)
  · haveI := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q)
  · haveI := h0; exact Module.Finite.equiv (kerEquiv F G K K' e he 0).symm
  · haveI := h q; exact Module.Finite.equiv (hSuccEquiv F G K K' e he q).symm

end CochainEquiv

end AlgebraicGeometry.OModulePresheaf

end

theorem solution
    {R : Type u} [CommRing R] {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (e : ∀ q, F.cochain K q ≃ₗ[R] G.cochain K' q) (he : ∀ q x, e (q + 1) (F.d K q x) = G.d K' q (e q x)) :
    F.CechFinite K ↔ G.CechFinite K' :=
  AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochainEquiv F G K K' e he
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
