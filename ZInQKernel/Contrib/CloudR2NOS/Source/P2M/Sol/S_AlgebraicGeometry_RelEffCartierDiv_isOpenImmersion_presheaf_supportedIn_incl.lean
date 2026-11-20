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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.lean
  Source sha256  : fbc089eb5b0e8498395346b463d6b5423a4892b07d90b2804c2cf9980226e422
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

import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsOpenImmersion.lift Scheme.Opens.range_ι Scheme IsOpenImmersion Scheme.Opens IsOpenImmersion.lift_fac RelEffCartierDiv.supportedIn RelEffCartierDiv.functor RelEffCartierDiv"
namespace RelEffCartierDiv
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelEffCartierDiv" "SupportedIn supportedInLocus supportedIn_pullbackAlong_iff supportedIn mem_supportedIn_iff functor functor_map_snd ext pullbackAlong"
w03_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens)

set_option backward.isDefEq.respectTransparency false in

theorem isOpenImmersion_presheaf_supportedIn_incl_aux :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g

  set x : (RelEffCartierDiv.functor f r).obj (op T) := yonedaEquiv g with hx
  have hg : ∀ {T' : Scheme.{u}ᵒᵖ} (φ : unop T' ⟶ T),
      g.app T' φ = (RelEffCartierDiv.functor f r).map φ.op x := by
    intro T' φ
    rw [hx, yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

  let W : T.Opens := x.2.supportedInLocus U
  have hxW : (RelEffCartierDiv.functor f r).map W.ι.op x ∈
      (RelEffCartierDiv.supportedIn f r U).obj (op (W : Scheme.{u})) := by
    rw [mem_supportedIn_iff, functor_map_snd]
    exact (supportedIn_pullbackAlong_iff _ _ _ _).mpr
      (by simp only [Quiver.Hom.unop_op, Scheme.Opens.range_ι]; exact subset_rfl)
  let y : (RelEffCartierDiv.supportedIn f r U).toFunctor.obj (op (W : Scheme.{u})) := ⟨_, hxW⟩
  refine ⟨W, yonedaEquiv.symm y, W.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  intro T'
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    refine ConcreteCategory.hom_ext _ _ fun ψ => ?_
    simp only [ConcreteCategory.comp_apply, yonedaEquiv_symm_app_apply, yoneda_map_app, hg]
    change (RelEffCartierDiv.functor f r).map ψ.op ((RelEffCartierDiv.functor f r).map W.ι.op x) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    rfl
  ·
    rintro ψ₁ ψ₂ ⟨-, h⟩
    simp only [yoneda_map_app] at h
    exact (cancel_mono W.ι).mp h
  ·
    intro y₂ φ h
    change unop T' ⟶ T at φ
    change y₂.1 = g.app T' φ at h
    rw [hg] at h
    have hφ : (x.2.pullbackAlong φ rfl).SupportedIn U := by
      have := y₂.2
      rw [h, mem_supportedIn_iff, functor_map_snd] at this
      exact this
    rw [supportedIn_pullbackAlong_iff] at hφ
    have hW : Set.range φ ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨IsOpenImmersion.lift W.ι φ hW, ?_, ?_⟩
    · apply Subtype.ext
      change (RelEffCartierDiv.functor f r).map (IsOpenImmersion.lift W.ι φ hW).op
        ((RelEffCartierDiv.functor f r).map W.ι.op x) = y₂.1
      rw [h, ← Functor.map_comp_apply, ← op_comp, IsOpenImmersion.lift_fac]
    · exact IsOpenImmersion.lift_fac W.ι φ hW

end AlgebraicGeometry.RelEffCartierDiv

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens) :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι :=
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl_aux f r U
end S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
