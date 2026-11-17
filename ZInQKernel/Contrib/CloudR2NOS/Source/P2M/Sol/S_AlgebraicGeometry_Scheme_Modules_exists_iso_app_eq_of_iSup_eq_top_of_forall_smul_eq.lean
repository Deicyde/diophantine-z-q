/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq.lean
  Source sha256  : bf56ca22397c3c1a197973acfbcefcba8eb3c6514e0c332faa2fd3ce8ea79b60
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
r2nos_namespace_dual
r2nos_erase_attr "instance" "SheafOfModules.isIso_ihomModelToIhom"
r2nos_erase_attr "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
r2nos_open_dual "CategoryTheory TopologicalSpace AlgebraicGeometry"

namespace P2mIsoGlue
r2nos_namespace_dual

variable {X : Scheme.{u}}

theorem map_map {M : X.Modules} {A B D : X.Opens} (hBA : B ≤ A) (hDB : D ≤ B) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE hDB).op (M.presheaf.map (homOfLE hBA).op s) =
      M.presheaf.map (homOfLE (hDB.trans hBA)).op s := by
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]; rfl

theorem map_irrel {M : X.Modules} {A B : X.Opens} (h h' : B ≤ A) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op s = M.presheaf.map (homOfLE h').op s := rfl

theorem map_le_refl {M : X.Modules} {A : X.Opens} (h : A ≤ A) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op s = s := by
  rw [Subsingleton.elim (homOfLE h) (𝟙 A), op_id, M.presheaf.map_id]; rfl

theorem map_smul' {M : X.Modules} {A B : X.Opens} (h : B ≤ A) (g : Γ(X, A)) (s : Γ(M, A)) :
    M.presheaf.map (homOfLE h).op (HSMul.hSMul g s) =
      HSMul.hSMul ((X.presheaf.map (homOfLE h).op).hom g) (M.presheaf.map (homOfLE h).op s) :=
  Scheme.Modules.map_smul M (homOfLE h) g s

variable {ι : Type u} (T : ι → X.Opens) {L L' : X.Modules}
  (s : ∀ k, Γ(L, T k)) (s' : ∀ k, Γ(L', T k))

theorem exists_transition (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) (i j : ι) : ∃ g : Γ(X, T i ⊓ T j),
    HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
      L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j) :=
  ((hs i) (inf_le_left : T i ⊓ T j ≤ T i) inf_le_left).2 _

theorem isUnit_of_transition (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) {i j : ι} {g : Γ(X, T i ⊓ T j)}
    (hg : HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
      L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j)) : IsUnit g := by
  obtain ⟨g', hg'⟩ := ((hs j) (inf_le_right : T i ⊓ T j ≤ T j) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i))
  have hg'' : HSMul.hSMul g' (L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j)) =
      L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i) := hg'
  refine IsUnit.of_mul_eq_one g' (((hs j) (inf_le_right : T i ⊓ T j ≤ T j) inf_le_right).1 ?_)
  change HSMul.hSMul (g * g') _ = HSMul.hSMul (1 : Γ(X, T i ⊓ T j)) _
  rw [mul_smul, hg'', hg, one_smul]

def S (W : X.Opens) : Set (Γ(L, W) × Γ(L', W)) :=
  {pq | ∃ (k : ι) (h : W ≤ T k), pq = (L.presheaf.map (homOfLE h).op (s k), L'.presheaf.map (homOfLE h).op (s' k))}

end P2mIsoGlue

open P2mIsoGlue in
r2nos_open_dual "P2mIsoGlue" in
theorem solution
    {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] (T : ι → X.Opens) (hT : ⨆ k, T k = ⊤)
    {L L' : X.Modules} (s : ∀ k, Γ(L, T k)) (s' : ∀ k, Γ(L', T k))
    (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) (hs' : ∀ k, Scheme.Modules.IsFrameOn (s' k) (T k))
    (h : ∀ (i j : ι), i < j → ∀ g : Γ(X, T i ⊓ T j),
      HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
          L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j) →
        HSMul.hSMul g (L'.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s' i)) =
          L'.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s' j)) :
    ∃ e : L ≅ L', ∀ k, e.hom.app (T k) (s k) = s' k := by

  have key : ∀ (k l : ι), k < l → ∀ (W : X.Opens) (hk : W ≤ T k) (hl : W ≤ T l), ∃ u : Γ(X, W),
      L.presheaf.map (homOfLE hl).op (s l) = HSMul.hSMul u (L.presheaf.map (homOfLE hk).op (s k)) ∧
      L'.presheaf.map (homOfLE hl).op (s' l) = HSMul.hSMul u (L'.presheaf.map (homOfLE hk).op (s' k)) ∧ IsUnit u := by
    intro k l hkl W hk hl
    obtain ⟨g, hg⟩ := exists_transition T s hs k l
    have hg' := h k l hkl g hg
    have hW : W ≤ T k ⊓ T l := le_inf hk hl
    refine ⟨(X.presheaf.map (homOfLE hW).op).hom g, ?_, ?_, (isUnit_of_transition T s hs hg).map _⟩
    · have := congrArg (L.presheaf.map (homOfLE hW).op) hg
      rw [map_smul', map_map, map_map] at this
      exact this.symm
    · have := congrArg (L'.presheaf.map (homOfLE hW).op) hg'
      rw [map_smul', map_map, map_map] at this
      exact this.symm
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_isFrameOn_of_eq_smul (S T s s')
    (fun W pq ⟨k, hk, hpq⟩ => by
      subst hpq
      exact ⟨((hs k).map (homOfLE hk)).mono hk, ((hs' k).map (homOfLE hk)).mono hk⟩)
    (fun x => by
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hT] at hx
      obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
      exact ⟨T k, hk, ⟨_, k, le_rfl, rfl⟩⟩)
    (fun W W' hW pq ⟨k, hk, hpq⟩ => by
      subst hpq
      exact ⟨k, hW.trans hk, by rw [map_map, map_map]⟩)
    (fun W pq pq' ⟨k, hk, hpq⟩ ⟨l, hl, hpq'⟩ => by
      subst hpq hpq'
      rcases lt_trichotomy k l with hkl | rfl | hlk
      · obtain ⟨u, h1, h2, -⟩ := key k l hkl W hk hl
        exact ⟨u, h1, h2⟩
      · exact ⟨1, by rw [one_smul], by rw [one_smul]⟩
      · obtain ⟨u, h1, h2, hu⟩ := key l k hlk W hl hk
        refine ⟨((hu.unit⁻¹ : Γ(X, W)ˣ) : Γ(X, W)), ?_, ?_⟩
        · change L.presheaf.map (homOfLE hl).op (s l) = HSMul.hSMul _ (L.presheaf.map (homOfLE hk).op (s k))
          rw [h1, ← mul_smul, IsUnit.val_inv_mul, one_smul]
        · change L'.presheaf.map (homOfLE hl).op (s' l) = HSMul.hSMul _ (L'.presheaf.map (homOfLE hk).op (s' k))
          rw [h2, ← mul_smul, IsUnit.val_inv_mul, one_smul])
  refine ⟨e, fun k => ?_⟩
  have := he (T k) (L.presheaf.map (homOfLE le_rfl).op (s k), L'.presheaf.map (homOfLE le_rfl).op (s' k))
    ⟨k, le_rfl, rfl⟩
  rwa [map_le_refl, map_le_refl] at this
end S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
