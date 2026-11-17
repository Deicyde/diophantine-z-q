/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq.lean
  Source sha256  : c942221dd1a7bf980f72f2e3f326befb3ef32d8b8f90319ad0775c6b920c2067
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * CANDIDATE 005 drift-adaptation (tools/drift_rules_v2.py, the rule set compiled-proven in the NOS-core probe loop), applied: T6×1
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace AlgebraicGeometry"
open AlgebraicGeometry.Scheme.Modules
r2nos_open_dual "AlgebraicGeometry.Scheme.Modules"

namespace N2P1
r2nos_namespace_dual

variable {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens}

theorem map_map (M : X.Modules) {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    M.presheaf.map (homOfLE h₃₂).op (M.presheaf.map (homOfLE h₂₁).op y) =
      M.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

theorem ihomSection_ext (p : Γ(P, V)) (hp : IsFrameOn p V) {θ θ' : Γ((ihom P).obj Q, V)}
    (h : ihomEval P Q V p θ = ihomEval P Q V p θ') : θ = θ' := by
  apply ihom_sections_ext
  intro W i m
  have hW : W ≤ V := i.le
  obtain ⟨g, rfl⟩ := (hp hW hW).2 m
  simp only
  have hi : i = homOfLE hW := Subsingleton.elim _ _
  subst hi
  rw [ihomEval_smul_left, ihomEval_smul_left, ← map_ihomEval, ← map_ihomEval, h]

noncomputable def coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) :
    Γ(P, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) Γ(P, W) (P.presheaf.map (homOfLE hW).op p))
    (hp hW hW)).symm

theorem coeff_smul (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (g : Γ(X, W)) :
    coeff p hp hW (g • P.presheaf.map (homOfLE hW).op p) = g := by
  apply (coeff p hp hW).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem smul_coeff (p : Γ(P, V)) (hp : IsFrameOn p V) {W : X.Opens} (hW : W ≤ V) (x : Γ(P, W)) :
    coeff p hp hW x • P.presheaf.map (homOfLE hW).op p = x := by
  obtain ⟨g, rfl⟩ := (hp hW hW).2 x
  simp only
  rw [coeff_smul]

theorem exists_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃ θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  classical

  let fam : PresheafOfModules.InternalHom.PiFamily ((toPMod X).obj P) ((toPMod X).obj Q) (op V) :=
    fun Y f =>
      (show Γ(P, Y.unop) →ₗ[Γ(X, Y.unop)] Γ(Q, Y.unop) from
        (LinearMap.toSpanSingleton Γ(X, Y.unop) Γ(Q, Y.unop) (Q.presheaf.map (homOfLE f.unop.le).op q)).comp
          (coeff p hp f.unop.le).toLinearMap)
  have fam_apply : ∀ {Y : (X.Opens)ᵒᵖ} (f : op V ⟶ Y) (x : Γ(P, Y.unop)),
      fam f x = coeff p hp f.unop.le x • Q.presheaf.map (homOfLE f.unop.le).op q := fun f x => rfl
  have hfam : PresheafOfModules.InternalHom.IsNatural fam := by
    intro Y Z f g x
    change Q.presheaf.map g (fam f x) = fam (f ≫ g) (P.presheaf.map g x)
    rw [fam_apply f, fam_apply (f ≫ g)]
    have hg : g = (homOfLE g.unop.le).op := Subsingleton.elim _ _
    rw [hg, Q.map_smul, map_map]
    congr 1

    symm
    apply (coeff p hp (f ≫ (homOfLE g.unop.le).op).unop.le).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change _ = (X.presheaf.map (homOfLE g.unop.le).op (coeff p hp f.unop.le x)) •
      P.presheaf.map (homOfLE _).op p
    conv_lhs => rw [← smul_coeff p hp f.unop.le x]
    rw [P.map_smul, map_map]
  let φ : PresheafOfModules.InternalHom.naturalFamilies ((toPMod X).obj P) ((toPMod X).obj Q) (op V) :=
    ⟨fam, hfam⟩
  refine ⟨(SheafOfModules.ihomSectionsEquivFamily X.sheaf.obj X.ringCatSheaf.property P Q (op V)).symm φ, ?_⟩
  change SheafOfModules.ihomEval X.sheaf.obj X.ringCatSheaf.property P Q (op V) p _ = q
  rw [SheafOfModules.ihomEval_def, AddEquiv.apply_symm_apply]
  change fam (𝟙 (op V)) p = q
  rw [fam_apply (𝟙 (op V))]
  change coeff p hp le_rfl p • Q.presheaf.map (homOfLE le_rfl).op q = q
  have h1 : coeff p hp (le_rfl : V ≤ V) p = 1 := by
    have := coeff_smul p hp (le_rfl : V ≤ V) 1
    rw [one_smul] at this
    have hp1 : P.presheaf.map (homOfLE (le_rfl : V ≤ V)).op p = p := by
      rw [Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, P.presheaf.map_id]; rfl
    rw [hp1] at this
    exact this
  rw [h1, one_smul, Subsingleton.elim (homOfLE (le_rfl : V ≤ V)) (𝟙 V), op_id, Q.presheaf.map_id]
  rfl

theorem exists_unique_ihomSection (p : Γ(P, V)) (hp : IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), ihomEval P Q V p θ = q := by
  obtain ⟨θ, hθ⟩ := exists_ihomSection p hp q
  exact ⟨θ, hθ, fun θ' hθ' => ihomSection_ext p hp (hθ'.trans hθ.symm)⟩

end N2P1

open AlgebraicGeometry _root_.AlgebraicGeometry in
r2nos_open_dual "AlgebraicGeometry" in
theorem solution {X : Scheme.{u}} {P Q : X.Modules} {V : X.Opens} {p : Γ(P, V)}
    (hp : Scheme.Modules.IsFrameOn p V) (q : Γ(Q, V)) :
    ∃! θ : Γ((ihom P).obj Q, V), Scheme.Modules.ihomEval P Q V p θ = q :=
  N2P1.exists_unique_ihomSection p hp q
end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
