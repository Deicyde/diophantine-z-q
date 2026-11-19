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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso.lean
  Source sha256  : 09504ca73b5843d8f0b08daa6d55680b53d572878ea991108061aa277a0c2bf8
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

def lbTB_tensorExchange {V : Type*} [Category V] [MonoidalCategory V] [BraidedCategory V]
    (A B C D : V) : (A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D) :=
  α_ A B (C ⊗ D) ≪≫ (Iso.refl A ⊗ᵢ ((α_ B C D).symm ≪≫ (β_ B C ⊗ᵢ Iso.refl D) ≪≫ α_ C B D)) ≪≫
    (α_ A C (B ⊗ D)).symm

theorem solution
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T)
    {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : P.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q ((Scheme.Modules.pullback q).obj N ⊗ L) ≅
      Scheme.Modules.rigidify σ q L) := by
  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨_, ⟨pairN⟩⟩ := Scheme.Modules.IsInvertible.dual hN
  obtain ⟨dt⟩ := Scheme.Modules.IsInvertible.dual_tensor hN hσL

  let eN : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj N) ≅ N :=
    (Scheme.Modules.pullbackComp σ q).app N ≪≫ (Scheme.Modules.pullbackCongr hσq).app N ≪≫
      (Scheme.Modules.pullbackId (X := T)).app N

  let eD : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj
      ((Scheme.Modules.pullback q).obj N ⊗ L)) ≅
      Scheme.Modules.dual N ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (eN ⊗ᵢ Iso.refl _)) ≪≫
      dt

  let eU : (Scheme.Modules.pullback q).obj N ⊗
      (Scheme.Modules.pullback q).obj (Scheme.Modules.dual N) ≅ 𝟙_ P.Modules :=
    (Scheme.Modules.pullbackTensorObjIso q N _).symm ≪≫ (Scheme.Modules.pullback q).mapIso pairN ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso q
  refine ⟨?_⟩
  change ((Scheme.Modules.pullback q).obj N ⊗ L) ⊗ (Scheme.Modules.pullback q).obj _ ≅
    L ⊗ (Scheme.Modules.pullback q).obj _
  exact (Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback q).mapIso eD ≪≫
      Scheme.Modules.pullbackTensorObjIso q _ _)) ≪≫
    lbTB_tensorExchange _ _ _ _ ≪≫ (eU ⊗ᵢ Iso.refl _) ≪≫ λ_ _
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
