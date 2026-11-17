/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.lean
  Source sha256  : 9fdb247cc807d33d43cf71e55ad79e2328c12d8264f40eca1e3fa13dec24202c
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
r2nos_namespace_dual
r2nos_erase_attr "instance" "SheafOfModules.isIso_ihomModelToIhom"
r2nos_erase_attr "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

w03_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.AlgebraicGeometry"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.map_smul Scheme.Modules.IsFrameOn Scheme.Modules.UnitCocycle Scheme.Modules.glueOfCocycle Scheme.Modules.glueFrame Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.map_glueFrame_eq_smul Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Γ Modules Opens Modules.map_smul Modules.IsFrameOn Modules.UnitCocycle Modules.glueOfCocycle Modules.glueFrame Modules.isFrameOn_glueFrame Modules.map_glueFrame_eq_smul Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf map_smul IsFrameOn UnitCocycle glueOfCocycle glueFrame isFrameOn_glueFrame map_glueFrame_eq_smul exists_iso_app_eq_of_isFrameOn_of_eq_smul"
namespace GlueRecon
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

w03_open "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {A B : X.Opens} (h : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

theorem map_refl {A : X.Opens} (m : Γ(M, A)) : M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, M.presheaf.map_id]; rfl

theorem isFrameOn_unit_smul_map {A W : X.Opens} (hW : W ≤ A) {s : Γ(M, A)} (hs : IsFrameOn s A)
    (g : Γ(X, W)) (hg : IsUnit g) : IsFrameOn (g • M.presheaf.map (homOfLE hW).op s) W := by
  intro W' hW'W _
  have hg' : IsUnit (X.presheaf.map (homOfLE hW'W).op g) := hg.map _
  obtain ⟨v, hv⟩ := hg'
  have hb := hs (hW'W.trans hW) (hW'W.trans hW)
  have hcomp : (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map (homOfLE hW).op s)) =
      (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE (hW'W.trans hW)).op s) ∘ (fun a => a * ↑v) := by
    funext a
    simp only [Function.comp_apply, map_smul', map_map, ← hv, smul_smul]
  rw [hcomp]
  exact hb.comp (Units.mulRight_bijective v)

end AlgebraicGeometry.Scheme.Modules.GlueRecon

open _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueRecon AlgebraicGeometry.Scheme.Modules.GlueOfCocycle in
r2nos_open_dual "_root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueRecon AlgebraicGeometry.Scheme.Modules.GlueOfCocycle" in
theorem solution
    {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (hU : ⨆ i, U i = ⊤) (c : Scheme.Modules.UnitCocycle U)
    {M : X.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) :
    ∃ φ : M ≅ Scheme.Modules.glueOfCocycle c, ∀ i, φ.hom.app (U i) (e i) = Scheme.Modules.glueFrame c i := by
  classical
  let G := Scheme.Modules.glueOfCocycle c
  let f : ∀ i, Γ(G, U i) := fun i => Scheme.Modules.glueFrame c i
  have hf : ∀ i, IsFrameOn (f i) (U i) := fun i => Scheme.Modules.isFrameOn_glueFrame c i
  have hftrans : ∀ i j, G.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (f j) =
      c.u i j • G.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (f i) :=
    fun i j => Scheme.Modules.map_glueFrame_eq_smul c i j

  let S : ∀ W : X.Opens, Set (Γ(M, W) × Γ(G, W)) := fun W =>
    {pq | ∃ (i : ι) (hW : W ≤ U i) (g : Γ(X, W)), IsUnit g ∧
      pq.1 = g • M.presheaf.map (homOfLE hW).op (e i) ∧ pq.2 = g • G.presheaf.map (homOfLE hW).op (f i)}
  have hframe : ∀ (W : X.Opens) (pq : Γ(M, W) × Γ(G, W)), pq ∈ S W → IsFrameOn pq.1 W ∧ IsFrameOn pq.2 W := by
    rintro W pq ⟨i, hW, g, hg, h1, h2⟩
    rw [h1, h2]
    exact ⟨isFrameOn_unit_smul_map hW (he i) g hg, isFrameOn_unit_smul_map hW (hf i) g hg⟩
  have hcov : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧ (S W).Nonempty := by
    intro x
    have hx : x ∈ (⨆ i, U i) := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i, hi, ⟨(M.presheaf.map (homOfLE (le_refl (U i))).op (e i), G.presheaf.map (homOfLE (le_refl (U i))).op (f i)),
      ⟨i, le_rfl, 1, isUnit_one, by rw [one_smul], by rw [one_smul]⟩⟩⟩
  have hres : ∀ (W W' : X.Opens) (h : W' ≤ W) (pq : Γ(M, W) × Γ(G, W)), pq ∈ S W →
      (M.presheaf.map (homOfLE h).op pq.1, G.presheaf.map (homOfLE h).op pq.2) ∈ S W' := by
    rintro W W' h pq ⟨i, hW, g, hg, h1, h2⟩
    refine ⟨i, h.trans hW, X.presheaf.map (homOfLE h).op g, hg.map _, ?_, ?_⟩
    · simp only [h1, map_smul', map_map]
    · simp only [h2, map_smul', map_map]
  have hunit : ∀ (W : X.Opens) (pq pq' : Γ(M, W) × Γ(G, W)), pq ∈ S W → pq' ∈ S W →
      ∃ w : Γ(X, W), pq'.1 = w • pq.1 ∧ pq'.2 = w • pq.2 := by
    rintro W pq pq' ⟨i, hW, g, hg, h1, h2⟩ ⟨j, hW', g', hg', h1', h2'⟩
    obtain ⟨v, hv⟩ := hg

    refine ⟨g' * rO (le_inf hW hW' : W ≤ U i ⊓ U j) (c.u i j) * ↑v⁻¹, ?_, ?_⟩
    ·
      have ht := congrArg (M.presheaf.map (homOfLE (le_inf hW hW' : W ≤ U i ⊓ U j)).op) (htrans i j)
      rw [map_smul', map_map, map_map] at ht
      rw [h1', h1, ← hv, smul_smul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← smul_smul]
      erw [ht]
    · have ht := congrArg (G.presheaf.map (homOfLE (le_inf hW hW' : W ≤ U i ⊓ U j)).op) (hftrans i j)
      rw [map_smul', map_map, map_map] at ht
      rw [h2', h2, ← hv, smul_smul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, ← smul_smul]
      erw [ht]
  obtain ⟨φ, hφ⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul S hframe hcov hres hunit
  refine ⟨φ, fun i => ?_⟩
  have hmem : (M.presheaf.map (homOfLE (le_refl (U i))).op (e i), G.presheaf.map (homOfLE (le_refl (U i))).op (f i)) ∈ S (U i) :=
    ⟨i, le_rfl, 1, isUnit_one, by rw [one_smul], by rw [one_smul]⟩
  have := hφ (U i) _ hmem
  rwa [map_refl, map_refl] at this
end S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
