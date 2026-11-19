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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean
  Source sha256  : c4a79086374401f3689d83c8156c6b34e210dc0d32d012386f97c6bc53d4c02d
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

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v}
    (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) : IsIso φ := by

  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x ↦
    TopologicalSpace.Opens.mem_iSup.mp (by rw [hU]; trivial)

  let F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  haveI : (Opens.grothendieckTopology X).HasSheafCompose (forget AddCommGrpCat.{u}) :=
    inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    ·
      refine ⟨fun {W} x y hxy p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      exact congrArg _ hxy
    ·
      refine ⟨fun {W} s p hp ↦ ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have hiso := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2
        (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      exact ⟨t, ht⟩

  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  have : IsIso (ψ.hom.app (Opposite.op V)) := by
    change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
    infer_instance
  exact this
end S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
