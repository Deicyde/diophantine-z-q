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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.lean
  Source sha256  : fe1b632166dca24209d4529e3d8c91f7d91efda1b5692e8e1e3465ebc0bc6931
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 9 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "forget Γ Modules Opens evaluation"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "toPresheaf pullback presheaf"
namespace FibreProductSections
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

noncomputable def evalForget (U : X.Opens) : TopCat.Presheaf Ab X ⥤ Type u :=
  (CategoryTheory.evaluation _ _).obj (op U) ⋙ CategoryTheory.forget Ab

noncomputable scoped instance (U : X.Opens) : PreservesLimitsOfShape WalkingCospan (evalForget (X := X) U) :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan
    ((CategoryTheory.evaluation (Opens X)ᵒᵖ Ab.{u}).obj (op U) ⋙ CategoryTheory.forget Ab.{u}))

noncomputable def sectionsFunctorAt (U : X.Opens) : X.Modules ⥤ Type u :=
  toPresheaf X ⋙ evalForget U

noncomputable scoped instance (U : X.Opens) :
    PreservesLimitsOfShape WalkingCospan (sectionsFunctorAt (X := X) U) := by
  unfold sectionsFunctorAt; infer_instance

theorem sectionsFunctorAt_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    (sectionsFunctorAt U).map φ x = φ.app U x := rfl

end AlgebraicGeometry.Scheme.Modules.FibreProductSections
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules.FibreProductSections"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme"
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry"

open CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FibreProductSections in
r2nos_open_dual "CategoryTheory.Limits _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.FibreProductSections" in

theorem solution
    {X : Scheme.{u}} {N₀ N₁ N₀₁ : X.Modules} (a : N₀ ⟶ N₀₁) (b : N₁ ⟶ N₀₁) :
    ∃ (L : X.Modules) (π₀ : L ⟶ N₀) (π₁ : L ⟶ N₁), π₀ ≫ a = π₁ ≫ b ∧
      (∀ U : X.Opens, Function.Injective fun s : Γ(L, U) => (π₀.app U s, π₁.app U s)) ∧
      (∀ (U : X.Opens) (s₀ : Γ(N₀, U)) (s₁ : Γ(N₁, U)), a.app U s₀ = b.app U s₁ →
        ∃ s : Γ(L, U), π₀.app U s = s₀ ∧ π₁.app U s = s₁) := by
  have key : ∀ U : X.Opens, ∃ e : (Γ(Limits.pullback a b, U) : Type u) ≃
      Types.PullbackObj ((sectionsFunctorAt U).map a) ((sectionsFunctorAt U).map b),
      ∀ s, (e s).1.1 = (pullback.fst a b).app U s ∧ (e s).1.2 = (pullback.snd a b).app U s := by
    intro U
    have hc := isLimitPullbackConeMapOfIsLimit (sectionsFunctorAt U) pullback.condition
      (pullbackIsPullback a b)
    exact ⟨PullbackCone.IsLimit.equivPullbackObj hc, fun s =>
      ⟨PullbackCone.IsLimit.equivPullbackObj_apply_fst hc s,
       PullbackCone.IsLimit.equivPullbackObj_apply_snd hc s⟩⟩
  refine ⟨Limits.pullback a b, pullback.fst a b, pullback.snd a b, pullback.condition, ?_, ?_⟩
  · intro U s t hst
    obtain ⟨e, he⟩ := key U
    apply e.injective
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [(he s).1, (he t).1]; exact congrArg Prod.fst hst
    · rw [(he s).2, (he t).2]; exact congrArg Prod.snd hst
  · intro U s₀ s₁ h
    obtain ⟨e, he⟩ := key U
    refine ⟨e.symm ⟨(s₀, s₁), h⟩, ?_, ?_⟩
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).1
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    · have := (he (e.symm ⟨(s₀, s₁), h⟩)).2
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
end S_AlgebraicGeometry_Scheme_Modules_exists_fibreProduct_sections_bijective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
