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
  Source file    : P2M/Sol/S_CategoryTheory_MorphismProperty_widePullback_base.lean
  Source sha256  : f0b77da5db447b47870190dffe4814095704f16dfb2490cb02900faec857e010
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 8 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 6 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_CategoryTheory_MorphismProperty_widePullback_base
r2nos_namespace_dual

set_option autoImplicit false

universe v u

w03_open "CategoryTheory P2MW.S_CategoryTheory_MorphismProperty_widePullback_base.CategoryTheory CategoryTheory.Limits P2MW.S_CategoryTheory_MorphismProperty_widePullback_base.CategoryTheory.Limits"

namespace CategoryTheory
r2nos_namespace_dual
w03_export "CategoryTheory" "Category MorphismProperty inv over IsIso"
namespace Limits
r2nos_namespace_dual
w03_export "CategoryTheory.Limits" "WidePullback.lift_π pullback.hom_ext WidePullback.lift_base_assoc WidePullback.lift_base HasPullbacks pullback.condition pullback WidePullback.lift_π_assoc WidePullback.π WidePullback.hom_ext pullback.snd WidePullback.π_arrow WidePullback.base widePullback WidePullback.lift HasFiniteWidePullbacks pullback.lift pullback.fst"
namespace WidePullback
r2nos_namespace_dual
w03_export "CategoryTheory.Limits.WidePullback" "lift_π lift_base_assoc lift_base lift_π_assoc π hom_ext π_arrow base lift"
w03_open "CategoryTheory.Limits.WidePullback CategoryTheory.Limits CategoryTheory"

attribute [local simp] WidePullback.lift_π WidePullback.lift_base WidePullback.lift_π_assoc
  WidePullback.lift_base_assoc

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

omit [HasPullbacks C] in

theorem isIso_base_of_isEmpty {J : Type} [Finite J] [IsEmpty J] {S : C} (X : J → C)
    (f : ∀ j, X j ⟶ S) : IsIso (WidePullback.base f) :=
  ⟨⟨WidePullback.lift (𝟙 S) (fun j => isEmptyElim j) (fun j => isEmptyElim j),
    by
      apply WidePullback.hom_ext
      · intro j; exact isEmptyElim j
      · simp,
    by simp⟩⟩

set_option backward.isDefEq.respectTransparency false in

noncomputable def succIsoPullback {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    widePullback S X f ≅
      pullback (f 0) (WidePullback.base fun i : Fin r => f i.succ) where
  hom := pullback.lift (WidePullback.π f 0)
    (WidePullback.lift (WidePullback.base f) (fun i => WidePullback.π f i.succ)
      (fun i => WidePullback.π_arrow f i.succ))
    (by simp [WidePullback.π_arrow])
  inv := WidePullback.lift
    (pullback.snd _ _ ≫ WidePullback.base fun i : Fin r => f i.succ)
    (fun j => Fin.cases (pullback.fst _ _)
      (fun i => pullback.snd _ _ ≫ WidePullback.π (fun i : Fin r => f i.succ) i) j)
    (fun j => by
      cases j using Fin.cases with
      | zero => simpa using pullback.condition
      | succ i => simp [WidePullback.π_arrow])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      cases j using Fin.cases with
      | zero => simp
      | succ i => simp
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · apply WidePullback.hom_ext
      · intro i; simp
      · simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem succIsoPullback_hom_snd_base {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    (succIsoPullback X f).hom ≫ pullback.snd _ _ ≫ (WidePullback.base fun i : Fin r => f i.succ) =
      WidePullback.base f := by
  simp [succIsoPullback]

end CategoryTheory.Limits.WidePullback

namespace CategoryTheory
r2nos_namespace_dual
w03_export "CategoryTheory" "Category MorphismProperty inv over IsIso"
namespace MorphismProperty
r2nos_namespace_dual
w03_export "CategoryTheory.MorphismProperty" "pullback_snd IsStableUnderBaseChange over IsMultiplicative pullbacks cancel_left_of_respectsIso under of_isIso comp_mem"
w03_open "CategoryTheory.MorphismProperty CategoryTheory"

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

theorem widePullback_base_aux {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} : ∀ {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S), (∀ i, P (f i)) →
      P (WidePullback.base f)
  | 0, X, f, _ => by
    have := WidePullback.isIso_base_of_isEmpty X f
    exact P.of_isIso _
  | r + 1, X, f, hf => by
    rw [← WidePullback.succIsoPullback_hom_snd_base X f, P.cancel_left_of_respectsIso]
    exact P.comp_mem _ _ (P.pullback_snd _ _ (hf 0))
      (widePullback_base_aux (fun i => X i.succ) (fun i => f i.succ) fun i => hf i.succ)

end CategoryTheory.MorphismProperty

theorem solution
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) :=
  CategoryTheory.MorphismProperty.widePullback_base_aux X f hf
end S_CategoryTheory_MorphismProperty_widePullback_base
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
