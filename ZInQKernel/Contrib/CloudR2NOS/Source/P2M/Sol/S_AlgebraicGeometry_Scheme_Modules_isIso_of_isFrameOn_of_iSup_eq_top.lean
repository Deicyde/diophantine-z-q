/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top.lean
  Source sha256  : 1b67d7351dcc45c190b0cd9b64f20a6b726915871b253be19ead1f94b2fa1b54
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * CANDIDATE 005 drift-adaptation (tools/drift_rules_v2.py, the rule set compiled-proven in the NOS-core probe loop), applied: T6×1
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
r2nos_open_dual "CategoryTheory Opposite TopologicalSpace AlgebraicGeometry"

namespace N2P4
r2nos_namespace_dual

open AlgebraicGeometry.Scheme.Modules
r2nos_open_dual "AlgebraicGeometry.Scheme.Modules"

variable {X : Scheme.{u}} {P Q : X.Modules}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem app_map (μ : P ⟶ Q) {V W : X.Opens} (h : W ≤ V) (x : Γ(P, V)) :
    μ.app W (P.presheaf.map (homOfLE h).op x) = Q.presheaf.map (homOfLE h).op (μ.app V x) := by
  have := (μ.mapPresheaf).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(P, V) → Γ(Q, W))) this) x

theorem app_injective_of_le (μ : P ⟶ Q) {V : X.Opens} (p : Γ(P, V)) (q : Γ(Q, V))
    (hp : IsFrameOn p V) (hq : IsFrameOn q V) (hμ : μ.app V p = q) {W : X.Opens} (hW : W ≤ V) :
    Function.Injective (μ.app W) := by
  intro x x' hxx'
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  obtain ⟨g', rfl⟩ := (hp hW hW).2 x'
  simp only [Scheme.Modules.Hom.app_smul, app_map, hμ] at hxx'
  have := (hq hW hW).1 hxx'
  rw [this]

theorem isIso_of_frames (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]

  let Wi : ι → X.Opens := fun i => W ⊓ 𝒱 i
  have hcovW : W ≤ ⨆ i, Wi i := by
    intro x hx
    have hx' : x ∈ (⨆ i, 𝒱 i : X.Opens) := by rw [hcov]; trivial
    rw [Opens.mem_iSup] at hx' ⊢
    obtain ⟨i, hi⟩ := hx'
    exact ⟨i, ⟨hx, hi⟩⟩
  let FP : TopCat.Sheaf Ab X.carrier := ⟨P.presheaf, P.isSheaf⟩
  let FQ : TopCat.Sheaf Ab X.carrier := ⟨Q.presheaf, Q.isSheaf⟩
  have hinjW : ∀ {W' : X.Opens} (i : ι), W' ≤ 𝒱 i → Function.Injective (μ.app W') :=
    fun i h => app_injective_of_le μ (p i) (q i) (hp i) (hq i) (hμ i) h
  constructor
  ·
    intro x x' h
    apply FP.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    apply hinjW i inf_le_right
    change μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x) =
      μ.app (Wi i) (P.presheaf.map (homOfLE inf_le_left).op x')
    rw [app_map, app_map]
    exact congrArg _ h
  ·
    intro y
    have hloc : ∀ i, ∃ x : Γ(P, Wi i), μ.app (Wi i) x = Q.presheaf.map (homOfLE inf_le_left).op y := by
      intro i
      obtain ⟨g, hg⟩ := (hq i (inf_le_right : Wi i ≤ 𝒱 i) inf_le_right).2
        (Q.presheaf.map (homOfLE inf_le_left).op y)
      refine ⟨g • P.presheaf.map (homOfLE (inf_le_right : Wi i ≤ 𝒱 i)).op (p i), ?_⟩
      rw [Scheme.Modules.Hom.app_smul, app_map, hμ i]
      exact hg
    choose x hx using hloc
    have hcomp : TopCat.Presheaf.IsCompatible FP.1 Wi x := by
      intro i j
      apply hinjW i (inf_le_left.trans inf_le_right)
      change μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_left).op (x i)) =
        μ.app (Wi i ⊓ Wi j) (P.presheaf.map (homOfLE inf_le_right).op (x j))
      rw [app_map, app_map, hx i, hx j, map_map, map_map]
    obtain ⟨s, hs, -⟩ := FP.existsUnique_gluing' Wi W (fun i => homOfLE inf_le_left) hcovW x hcomp
    refine ⟨show Γ(P, W) from s, ?_⟩
    apply FQ.eq_of_locally_eq' Wi W (fun i => homOfLE inf_le_left) hcovW
    intro i
    change Q.presheaf.map (homOfLE inf_le_left).op (μ.app W s) = Q.presheaf.map (homOfLE inf_le_left).op y
    rw [← app_map, ← hx i]
    exact congrArg _ (hs i)

end N2P4

open AlgebraicGeometry _root_.AlgebraicGeometry in
r2nos_open_dual "AlgebraicGeometry" in
theorem solution {X : Scheme.{u}} {P Q : X.Modules} (μ : P ⟶ Q) {ι : Type v} (𝒱 : ι → X.Opens) (hcov : ⨆ i, 𝒱 i = ⊤)
    (p : ∀ i, Γ(P, 𝒱 i)) (q : ∀ i, Γ(Q, 𝒱 i))
    (hp : ∀ i, Scheme.Modules.IsFrameOn (p i) (𝒱 i)) (hq : ∀ i, Scheme.Modules.IsFrameOn (q i) (𝒱 i))
    (hμ : ∀ i, μ.app (𝒱 i) (p i) = q i) : IsIso μ :=
  N2P4.isIso_of_frames μ 𝒱 hcov p q hp hq hμ
end S_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
