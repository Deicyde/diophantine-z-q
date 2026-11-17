/-
NEW EDITION (H5 lane4 a940f2af, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite.lean
  Source sha256  : c47ee3a6fa167aaf1c5cc2e21d017c4bf05f86985f977bce87fb307b424f2615
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_descendsAlong_surjective_inf_flat_inf_quasiCompact
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory hiding IsDiscrete
r2nos_open_dual "CategoryTheory~IsDiscrete"
w03_open "CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry"

namespace QFPtDesc
r2nos_namespace_dual

theorem sfq {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (Spec.map (q.residueFieldMap x)) := by
  refine ⟨⟨⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  letI := (q.residueFieldMap x).hom.toAlgebra
  show Module.Flat (Y.residueField (q x)) (X.residueField x)
  infer_instance

theorem locallyQuasiFinite_fiberToSpecResidueField
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyQuasiFinite f'] (y' : Y') :
    LocallyQuasiFinite (f.fiberToSpecResidueField (q y')) := by
  haveI := AlgebraicGeometry.LocallyQuasiFinite.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
  have sq' := isPullback_fiberToSpecResidueField_of_isPullback sq y'
  have hf' : LocallyQuasiFinite (f'.fiberToSpecResidueField y') :=
    MorphismProperty.pullback_snd (P := @LocallyQuasiFinite) f' (Y'.fromSpecResidueField y') inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyQuasiFinite)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq'.flip (sfq q y') hf'

theorem main
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]

  have hlqf : LocallyQuasiFinite (f.fiberToSpecResidueField (f x)) := by
    rw [hx]; exact locallyQuasiFinite_fiberToSpecResidueField sq y'
  have hdisc : _root_.IsDiscrete ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) :=
    (f.fiberToSpecResidueField (f x)).isDiscrete_preimage_singleton _
  have huniv : ((f.fiberToSpecResidueField (f x)) ⁻¹'
      {(f.fiberToSpecResidueField (f x)) (f.asFiber x)}) = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [huniv, isDiscrete_univ_iff] at hdisc
  exact isOpen_discrete _

end QFPtDesc

theorem solution
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} {q : Y' ⟶ Y}
    (sq : IsPullback p f' f q) [LocallyOfFiniteType f] [LocallyQuasiFinite f'] (y' : Y') (x : X)
    (hx : f x = q y') : f.QuasiFiniteAt x :=
  QFPtDesc.main sq y' x hx
end S_AlgebraicGeometry_Scheme_Hom_quasiFiniteAt_of_isPullback_of_locallyQuasiFinite
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
