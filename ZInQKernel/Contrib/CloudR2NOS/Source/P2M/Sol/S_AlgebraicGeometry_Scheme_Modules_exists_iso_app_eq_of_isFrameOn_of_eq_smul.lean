/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.lean
  Source sha256  : d2a1fe8a1b688b10717363a277965dbc4f4f51d85e2c8aa705aa7e239ff84687
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_existsUnique_ihomEval_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace"
w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.IsFrameOn"
namespace FrameTorsorGlue
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

variable {X : Scheme.{u}} {P Q : X.Modules}

theorem map_le_refl {M : X.Modules} {W : X.Opens} (t : Γ(M, W)) :
    M.presheaf.map (homOfLE (le_refl W)).op t = t := by
  rw [Subsingleton.elim (homOfLE (le_refl W)) (𝟙 W), op_id, M.presheaf.map_id]; rfl

theorem isUnit_of_isFrameOn_smul {M : X.Modules} {W : X.Opens} {p : Γ(M, W)} {u : Γ(X, W)}
    (hp : IsFrameOn p W) (hp' : IsFrameOn (u • p) W) : IsUnit u := by

  obtain ⟨w, hw⟩ := (hp' (le_refl W) (le_refl W)).2 p
  simp only [map_le_refl] at hw
  have h1 : (w * u) • p = (1 : Γ(X, W)) • p := by rw [mul_smul, hw, one_smul]
  have hinj := (hp (le_refl W) (le_refl W)).1
  simp only [map_le_refl] at hinj
  have hwu : w * u = 1 := hinj h1
  exact IsUnit.of_mul_eq_one_right w hwu

noncomputable def theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W)) :
    Γ((ihom P).obj Q, W) :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).choose

theorem ihomEval_theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W)) :
    ihomEval P Q W p (theta p hp q) = q :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).choose_spec.1

theorem eq_theta {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    {θ : Γ((ihom P).obj Q, W)} (h : ihomEval P Q W p θ = q) : θ = theta p hp q :=
  (IsFrameOn.existsUnique_ihomEval_eq (Q := Q) hp q).unique h (ihomEval_theta p hp q)

theorem map_theta {W W' : X.Opens} (h : W' ≤ W) (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    (hp' : IsFrameOn (P.presheaf.map (homOfLE h).op p) W') :
    ((ihom P).obj Q).presheaf.map (homOfLE h).op (theta p hp q) =
      theta (P.presheaf.map (homOfLE h).op p) hp' (Q.presheaf.map (homOfLE h).op q) := by
  apply eq_theta
  rw [← map_ihomEval, ihomEval_theta]

theorem theta_indep {W : X.Opens} (p : Γ(P, W)) (hp : IsFrameOn p W) (q : Γ(Q, W))
    (u : Γ(X, W)) (hp' : IsFrameOn (u • p) W) :
    theta (u • p) hp' (u • q) = theta p hp q := by
  apply eq_theta
  have hu : IsUnit u := isUnit_of_isFrameOn_smul hp hp'
  have h2 := ihomEval_theta (Q := Q) (u • p) hp' (u • q)
  rw [ihomEval_smul_left] at h2
  exact hu.smul_left_cancel.mp h2

theorem main (S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)))
    (hframe : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      IsFrameOn pq.1 W ∧ IsFrameOn pq.2 W)
    (hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty)
    (hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W')
    (hunit : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
      ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) :
    ∃ e : P ≅ Q, ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → e.hom.app W pq.1 = pq.2 := by
  classical

  let Th : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → Γ((ihom P).obj Q, W) :=
    fun W pq h => theta pq.1 (hframe W pq h).1 pq.2

  have indep : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)) (h : pq ∈ S W) (h' : pq' ∈ S W),
      Th W pq h = Th W pq' h' := by
    intro W pq pq' h h'
    obtain ⟨u, h1, h2⟩ := hunit W pq pq' h h'
    obtain ⟨p', q'⟩ := pq'
    simp only at h1 h2
    subst h1
    subst h2
    exact (theta_indep pq.1 (hframe W pq h).1 pq.2 u (hframe W _ h').1).symm

  have res : ∀ (W W' : X.Opens) (hle : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)) (h : pq ∈ S W),
      ((ihom P).obj Q).presheaf.map (homOfLE hle).op (Th W pq h) = Th W' _ (hres W W' hle pq h) :=
    fun W W' hle pq h => map_theta hle pq.1 (hframe W pq h).1 pq.2 _

  have hdata : ∀ x : X, ∃ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), x ∈ W ∧ pq ∈ S W := by
    intro x
    obtain ⟨W, hx, pq, hpq⟩ := hcov x
    exact ⟨W, pq, hx, hpq⟩
  choose W pq hx hpq using hdata
  have hcovW : (⊤ : X.Opens) ≤ ⨆ x, W x := fun x _ => Opens.mem_iSup.mpr ⟨x, hx x⟩

  let θ : ∀ x, Γ((ihom P).obj Q, W x) := fun x => Th (W x) (pq x) (hpq x)
  let FH : TopCat.Sheaf Ab X.carrier := ⟨((ihom P).obj Q).presheaf, ((ihom P).obj Q).isSheaf⟩
  have hcomp : TopCat.Presheaf.IsCompatible FH.1 W θ := by
    intro x z
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op (θ x) =
      ((ihom P).obj Q).presheaf.map (homOfLE inf_le_right).op (θ z)
    simp only [θ]
    rw [res _ _ inf_le_left _ (hpq x), res _ _ inf_le_right _ (hpq z)]
    exact indep _ _ _ (hres _ _ inf_le_left _ (hpq x)) (hres _ _ inf_le_right _ (hpq z))
  obtain ⟨Θ, hΘ, -⟩ := FH.existsUnique_gluing' W ⊤ (fun x => homOfLE le_top) hcovW θ hcomp

  have hΘW : ∀ (V : X.Opens) (rs : Γ(P, V) × Γ(Q, V)) (h : rs ∈ S V),
      ((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ = Th V rs h := by
    intro V rs h

    apply FH.eq_of_locally_eq' (fun x => V ⊓ W x) V (fun x => homOfLE inf_le_left)
      (fun v hv => Opens.mem_iSup.mpr ⟨v, hv, hx v⟩)
    intro x
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op
        (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) =
      ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op (Th V rs h)
    rw [res V (V ⊓ W x) inf_le_left rs h]
    have e1 : ((ihom P).obj Q).presheaf.map (homOfLE inf_le_left).op
        (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) =
        ((ihom P).obj Q).presheaf.map (homOfLE (inf_le_right : V ⊓ W x ≤ W x)).op
          (((ihom P).obj Q).presheaf.map (homOfLE le_top).op Θ) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply, ← Functor.map_comp]
      rfl
    rw [e1, hΘ x]
    change ((ihom P).obj Q).presheaf.map (homOfLE inf_le_right).op (Th (W x) (pq x) (hpq x)) = _
    rw [res (W x) (V ⊓ W x) inf_le_right (pq x) (hpq x)]
    exact indep _ _ _ (hres _ _ inf_le_right _ (hpq x)) (hres _ _ inf_le_left _ h)

  let μ : P ⟶ Q := ihomGlobalSectionsEquiv P Q Θ
  have hμ : ∀ (V : X.Opens) (rs : Γ(P, V) × Γ(Q, V)), rs ∈ S V → μ.app V rs.1 = rs.2 := by
    intro V rs h
    rw [ihomGlobalSectionsEquiv_app_apply, hΘW V rs h]
    exact ihomEval_theta _ _ _
  haveI : IsIso μ := isIso_of_isFrameOn_of_iSup_eq_top μ W (top_le_iff.mp hcovW)
    (fun x => (pq x).1) (fun x => (pq x).2)
    (fun x => (hframe _ _ (hpq x)).1) (fun x => (hframe _ _ (hpq x)).2) (fun x => hμ _ _ (hpq x))
  exact ⟨asIso μ, hμ⟩

end AlgebraicGeometry.FrameTorsorGlue

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul.AlgebraicGeometry" in
theorem solution
    {X : Scheme.{u}} {P Q : X.Modules} (S : ∀ W : X.Opens, Set (Γ(P, W) × Γ(Q, W)))
    (hframe : ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      Scheme.Modules.IsFrameOn pq.1 W ∧ Scheme.Modules.IsFrameOn pq.2 W)
    (hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty)
    (hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W →
      (P.presheaf.map (homOfLE h).op pq.1, Q.presheaf.map (homOfLE h).op pq.2) ∈ S W')
    (hunit : ∀ (W : X.Opens) (pq pq' : Γ(P, W) × Γ(Q, W)), pq ∈ S W → pq' ∈ S W →
      ∃ u : Γ(X, W), pq'.1 = u • pq.1 ∧ pq'.2 = u • pq.2) :
    ∃ e : P ≅ Q, ∀ (W : X.Opens) (pq : Γ(P, W) × Γ(Q, W)), pq ∈ S W → e.hom.app W pq.1 = pq.2 := by
  exact FrameTorsorGlue.main S hframe hcov hres hunit
end S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
