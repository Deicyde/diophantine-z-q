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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.lean
  Source sha256  : 299c6701eaab846f712e3779a3255e9ea51cc88bab283c866c4f46b3f7376705
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T1×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

set_option autoImplicit false

section

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme IsSeparated IsAffineOpen OModulePresheaf.Leray.restrictToPreimage OModulePresheaf.Leray.relHPresheaf Scheme.OrderedAffineCover OModulePresheaf Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections Scheme.OrderedAffineCoverOf.res Scheme.OrderedAffineCoverOf.d_apply"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "Leray.restrictToPreimage Leray.relHPresheaf res_res cochain d d_apply H0 HSucc res obj moduleSections"
namespace Leray
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Leray" "inter_restrictToPreimage restrictToPreimage relAltC relAltd relAltd_apply' relAltHB relHPresheaf"
namespace CoverMatch
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}

theorem res_res {O₁ O₂ O₃ : V'.Opens} (h₂₁ : O₂ ≤ O₁) (h₃₂ : O₃ ≤ O₂) (x : Γ(V', O₁)) :
    (V'.presheaf.map (homOfLE h₃₂).op).hom ((V'.presheaf.map (homOfLE h₂₁).op).hom x)
      = (V'.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_self {O : V'.Opens} (h : O ≤ O) (x : Γ(V', O)) :
    (V'.presheaf.map (homOfLE h).op).hom x = x := by
  rw [Subsingleton.elim (homOfLE h).op (𝟙 (op O)), V'.presheaf.map_id]
  rfl

variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsSeparated πZ]
variable (K' : Scheme.OrderedAffineCover V') {U : Z.Opens} (hU : IsAffineOpen U)

def cochainEquiv (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    relAltC p πZ K' U b ≃ₗ[R] (restrictToPreimage p πZ K' hU).cochain b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f τ => (V'.presheaf.map
      (homOfLE (inter_restrictToPreimage p πZ K' hU τ).le).op).hom (f τ)
    invFun := fun g τ => (V'.presheaf.map
      (homOfLE (inter_restrictToPreimage p πZ K' hU τ).ge).op).hom (g τ)
    left_inv := fun f => funext fun τ => by
      show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (f τ)) = f τ
      rw [res_res, res_self]
    right_inv := fun g => funext fun τ => by
      show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (g τ)) = g τ
      rw [res_res, res_self]
    map_add' := fun _ _ => funext fun τ => map_add _ _ _
    map_smul' := fun r f => funext fun τ =>
      (Scheme.OrderedAffineCoverOf.res (p ≫ πZ)
        (inter_restrictToPreimage p πZ K' hU τ).le).map_smul r (f τ) }

theorem cochainEquiv_apply (b : ℕ) (f : relAltC p πZ K' U b) (τ : (restrictToPreimage p πZ K' hU).Idx b) :
    cochainEquiv p πZ K' hU b f τ
      = (V'.presheaf.map (homOfLE (inter_restrictToPreimage p πZ K' hU τ).le).op).hom (f τ) :=
  rfl

theorem cochainEquiv_relAltd (b : ℕ) (f : relAltC p πZ K' U b) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    cochainEquiv p πZ K' hU (b + 1) (relAltd p πZ K' U b f)
      = (restrictToPreimage p πZ K' hU).d (p ≫ πZ) b (cochainEquiv p πZ K' hU b f) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  funext τ
  rw [cochainEquiv_apply, relAltd_apply', Scheme.OrderedAffineCoverOf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, cochainEquiv_apply, res_res, res_res]
  rfl

def kerEquiv (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    LinearMap.ker (relAltd p πZ K' U b)
      ≃ₗ[R] LinearMap.ker ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  LinearEquiv.ofLinear
    ((cochainEquiv p πZ K' hU b).toLinearMap.restrict fun x hx =>
      LinearMap.mem_ker.mpr
        (((cochainEquiv_relAltd p πZ K' hU b x).symm.trans
          (congrArg (cochainEquiv p πZ K' hU (b + 1)) (LinearMap.mem_ker.mp hx))).trans
          (map_zero _)))
    ((cochainEquiv p πZ K' hU b).symm.toLinearMap.restrict fun y hy =>
      LinearMap.mem_ker.mpr ((cochainEquiv p πZ K' hU (b + 1)).injective
        ((cochainEquiv_relAltd p πZ K' hU b _).trans
          (((congrArg ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b)
              ((cochainEquiv p πZ K' hU b).apply_symm_apply y)).trans
            (LinearMap.mem_ker.mp hy)).trans (map_zero _).symm))))
    (LinearMap.ext fun y => Subtype.ext
      ((cochainEquiv p πZ K' hU b).apply_symm_apply y.1))
    (LinearMap.ext fun x => Subtype.ext
      ((cochainEquiv p πZ K' hU b).symm_apply_apply x.1))

theorem kerEquiv_apply_coe (b : ℕ)
    (x : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ); ↥(LinearMap.ker (relAltd p πZ K' U b))) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ((kerEquiv p πZ K' hU b x : LinearMap.ker ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b))
        : (restrictToPreimage p πZ K' hU).cochain b)
      = cochainEquiv p πZ K' hU b x.1 :=
  rfl

theorem kerEquiv_symm_apply_coe (b : ℕ)
    (y : letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
      ↥(LinearMap.ker ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b))) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (((kerEquiv p πZ K' hU b).symm y : LinearMap.ker (relAltd p πZ K' U b)) : relAltC p πZ K' U b)
      = (cochainEquiv p πZ K' hU b).symm y.1 :=
  rfl

def H0Equiv :
    (relHPresheaf p πZ K' 0).obj U ≃ₗ[R] (restrictToPreimage p πZ K' hU).H0 (p ≫ πZ) :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  (Submodule.quotEquivOfEqBot (relAltHB p πZ K' U 0) rfl).trans (kerEquiv p πZ K' hU 0)

theorem relAltHB_map_kerEquiv (b : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (relAltHB p πZ K' U (b + 1)).map (kerEquiv p πZ K' hU (b + 1)).toLinearMap
      = (LinearMap.range ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b)).comap
          (LinearMap.ker ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) (b + 1))).subtype := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr ?_) ?_
  · rintro x ⟨y, hy⟩
    exact ⟨cochainEquiv p πZ K' hU b y,
      (cochainEquiv_relAltd p πZ K' hU b y).symm.trans (congrArg (cochainEquiv p πZ K' hU (b + 1)) hy)⟩
  · rintro y ⟨g, hg⟩
    refine ⟨(kerEquiv p πZ K' hU (b + 1)).symm y, ⟨(cochainEquiv p πZ K' hU b).symm g, ?_⟩,
      (kerEquiv p πZ K' hU (b + 1)).apply_symm_apply y⟩
    show _ = (cochainEquiv p πZ K' hU (b + 1)).symm y.1
    apply (cochainEquiv p πZ K' hU (b + 1)).injective
    rw [cochainEquiv_relAltd, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hg

def HSuccEquiv (b : ℕ) :
    (relHPresheaf p πZ K' (b + 1)).obj U ≃ₗ[R] (restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  Submodule.Quotient.equiv (relAltHB p πZ K' U (b + 1))
    ((LinearMap.range ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) b)).comap
      (LinearMap.ker ((restrictToPreimage p πZ K' hU).d (p ≫ πZ) (b + 1))).subtype)
    (kerEquiv p πZ K' hU (b + 1)) (relAltHB_map_kerEquiv p πZ K' hU b)

end AlgebraicGeometry.OModulePresheaf.Leray.CoverMatch

end

end

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Leray _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.AlgebraicGeometry.OModulePresheaf.Leray in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Leray _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen.AlgebraicGeometry.OModulePresheaf.Leray" in

theorem solution
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ]
    (K' : V'.OrderedAffineCover) {U : Z.Opens} (hU : IsAffineOpen U) :
    Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' 0).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).H0 (p ≫ πZ)) ∧
      ∀ b : ℕ, Nonempty ((OModulePresheaf.Leray.relHPresheaf p πZ K' (b + 1)).obj U
        ≃ₗ[R] (OModulePresheaf.Leray.restrictToPreimage p πZ K' hU).HSucc (p ≫ πZ) b) :=
  ⟨⟨CoverMatch.H0Equiv p πZ K' hU⟩, fun b => ⟨CoverMatch.HSuccEquiv p πZ K' hU b⟩⟩
end S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
