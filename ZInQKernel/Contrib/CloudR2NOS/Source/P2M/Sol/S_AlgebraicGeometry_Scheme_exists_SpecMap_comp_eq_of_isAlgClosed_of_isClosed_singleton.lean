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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton.lean
  Source sha256  : 59de1f58a48259d7bb27f87eb9e81a03708860b797c86b42ef1d74515b1cd1a2
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

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
r2nos_open_dual "CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite"

theorem solution
    {k₀ : Type u} [Field k₀] {F : Scheme.{u}} (f : F ⟶ Spec (CommRingCat.of k₀)) [LocallyOfFiniteType f]
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosed k]
    (y : F) (hy : IsClosed ({y} : Set F)) :
    ∃ z : Spec (CommRingCat.of k) ⟶ F,
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ∧ z.base (IsLocalRing.closedPoint k) = y := by

  set g := F.fromSpecResidueField y ≫ f with hg
  have hfin : IsFinite g := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hy
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := g)).mpr inferInstance
  let φ : CommRingCat.of k₀ ⟶ F.residueField y := Spec.preimage g
  have hφ : Spec.map φ = g := Spec.map_preimage g
  have hint : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ]
    infer_instance
  letI : Algebra k₀ (F.residueField y) := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral k₀ (F.residueField y) := ⟨hint⟩

  let ψ : F.residueField y →ₐ[k₀] k := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← hφ, ← Spec.map_comp]
    congr 1
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
    exact ψ.commutes a
  · have hmem : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ F.fromSpecResidueField y).base
        (IsLocalRing.closedPoint k) ∈ Set.range (F.fromSpecResidueField y).base :=
      ⟨(Spec.map (CommRingCat.ofHom ψ.toRingHom)).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem
end S_AlgebraicGeometry_Scheme_exists_SpecMap_comp_eq_of_isAlgClosed_of_isClosed_singleton
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
