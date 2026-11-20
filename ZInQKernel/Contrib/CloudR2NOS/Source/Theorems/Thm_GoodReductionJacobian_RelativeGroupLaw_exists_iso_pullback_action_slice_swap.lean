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
  Source file    : Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap.lean
  Source sha256  : 514c6842b30d1ddbb557d8ef92ccb535b166f91feb6c51448b7499b5e0b276ff
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_action_slice_swap
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) :
    ∃ σ : CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≅
        CategoryTheory.Limits.pullback (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j,
      σ.hom ≫ CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j =
        (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ∧
      σ.hom ≫ (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) =
        CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_action_slice_swap.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
