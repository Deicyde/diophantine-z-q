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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.lean
  Source sha256  : d54ba512d643302e1697c451f07b52d324a08e04a4c169d55e4f32371478c70a
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_iff_of_cochain_equiv
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Finiteness.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme IsClosedImmersion OModulePresheaf.pushforward OModulePresheaf OModulePresheaf.d_apply OModulePresheaf.cechFinite_iff_of_cochain_equiv"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "zero pushforward pushforward_res cochain d d_apply CechFinite res res_refl obj res_comp cechFinite_iff_of_cochain_equiv"
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section Transport

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {ρ : Z ⟶ Spec (.of R)} (H : OModulePresheaf ρ)

def resEq {U U' : Z.Opens} (h : U = U') : H.obj U ≃ₗ[R] H.obj U' where
  toFun := H.res h.ge
  invFun := H.res h.le
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    show (H.res h.le ∘ₗ H.res h.ge) x = x
    rw [← H.res_comp]; exact LinearMap.congr_fun (H.res_refl U) x
  right_inv x := by
    show (H.res h.ge ∘ₗ H.res h.le) x = x
    rw [← H.res_comp]; exact LinearMap.congr_fun (H.res_refl U') x

theorem resEq_apply {U U' : Z.Opens} (h : U = U') (x : H.obj U) : resEq H h x = H.res h.ge x := rfl

theorem res_res_apply {U₁ U₂ U₃ : Z.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (x : H.obj U₁) :
    H.res h₂ (H.res h₁ x) = H.res (h₂.trans h₁) x := by
  rw [← LinearMap.comp_apply, ← H.res_comp]

end Transport

section Pushforward

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
variable (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover)

theorem map_iInf_fin' {X Y : Scheme.{u}} (f : X ⟶ Y) {n : ℕ} (U : Fin (n + 1) → Y.Opens) :
    (Opens.map f.base).obj (⨅ j, U j) = ⨅ j, (Opens.map f.base).obj (U j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero => simp only [show (⨅ j : Fin 1, U j) = U 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, (Opens.map f.base).obj (U j)) = (Opens.map f.base).obj (U 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit U, show (Opens.map f.base).obj (U 0 ⊓ (⨅ j : Fin (m + 1), U j.succ))
        = (Opens.map f.base).obj (U 0) ⊓ (Opens.map f.base).obj (⨅ j : Fin (m + 1), U j.succ)
      from rfl, ih (fun j => U j.succ), hsplit (fun j => (Opens.map f.base).obj (U j))]

theorem inter_preimage {q : ℕ} (s : (K.preimage i).Idx q) :
    (K.preimage i).inter s = i ⁻¹ᵁ K.inter (show K.Idx q from s) :=
  (map_iInf_fin' i _).symm

def pushforwardCochainEquiv (q : ℕ) : H.cochain (K.preimage i) q ≃ₗ[R] (pushforward π i H).cochain K q :=
  LinearEquiv.piCongrRight fun s => resEq H (inter_preimage i K s)

theorem pushforwardCochainEquiv_d (q : ℕ) (x : H.cochain (K.preimage i) q) :
    pushforwardCochainEquiv i H K (q + 1) (H.d (K.preimage i) q x)
      = (pushforward π i H).d K q (pushforwardCochainEquiv i H K q x) := by
  funext s
  show resEq H (inter_preimage i K s) (H.d (K.preimage i) q x s) = (pushforward π i H).d K q _ s
  rw [resEq_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, pushforward_res, res_res_apply]
  congr 1
  show _ = H.res _ (resEq H (inter_preimage i K _) (x _))
  rw [resEq_apply, res_res_apply]
  rfl

end Pushforward

end AlgebraicGeometry.OModulePresheaf

end

theorem solution
    {R : Type u} [CommRing R] {V Z : Scheme.{u}} {π : V ⟶ Spec (.of R)} (i : Z ⟶ V) [IsClosedImmersion i]
    (H : OModulePresheaf (i ≫ π)) (K : V.OrderedAffineCover) :
    (OModulePresheaf.pushforward π i H).CechFinite K ↔ H.CechFinite (K.preimage i) :=
  (AlgebraicGeometry.OModulePresheaf.cechFinite_iff_of_cochain_equiv H (OModulePresheaf.pushforward π i H)
    (K.preimage i) K (AlgebraicGeometry.OModulePresheaf.pushforwardCochainEquiv i H K)
    (AlgebraicGeometry.OModulePresheaf.pushforwardCochainEquiv_d i H K)).symm
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
