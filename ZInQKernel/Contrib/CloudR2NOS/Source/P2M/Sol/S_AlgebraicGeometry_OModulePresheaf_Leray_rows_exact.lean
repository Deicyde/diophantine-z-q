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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.lean
  Source sha256  : 2a586af63ee86b296c9aaa82bffed39a2969a5fcd87607595f6195aae7215591
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T1×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.AlgebraicGeometry TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme IsSeparated OModulePresheaf.Leray.LerayDblCpx OModulePresheaf.Leray.biAug Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.d OModulePresheaf.unit Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.res_res Scheme.OrderedAffineCoverOf Scheme.OrderedAffineCoverOf.moduleSections Scheme.OrderedAffineCoverOf.res Scheme.OrderedAffineCoverOf.d_apply Scheme.OrderedAffineCoverOf.aug_apply Scheme.OrderedAffineCover.d_toCoverOf Scheme.OrderedAffineCover.isAffineOpen_inter Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug Scheme.OrderedAffineCoverOf.aug_injective"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "Leray.LerayDblCpx Leray.biAug res_res cochain d d_apply unit res obj moduleSections"
namespace Leray
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Leray" "LerayDblCpx biAug biAug_apply rowCoverOf inter_rowCoverOf biOpen dH pullOpen biC_uncurry' dH_uncurry"
w03_open "AlgebraicGeometry.OModulePresheaf.Leray AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section Aux

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem res_self' {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) : (V.presheaf.map (homOfLE h).op).hom x = x := by
  rw [show (homOfLE h : O ⟶ O) = 𝟙 O from rfl, op_id, V.presheaf.map_id]; rfl

theorem unit_d_apply' (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover) (i : ℕ)
    (f : (OModulePresheaf.unit π).cochain K i) (s : K.Idx (i + 1)) :
    ((OModulePresheaf.unit π).d K i f s : Γ(V, K.inter s))
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom (f (K.face s j)) := by
  rw [← Scheme.OrderedAffineCover.d_toCoverOf]
  exact Scheme.OrderedAffineCoverOf.d_apply π K.toCoverOf i f s

end Aux

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (CommRingCat.of R))
variable (K : Scheme.OrderedAffineCover Z) (K' : Scheme.OrderedAffineCover V')

theorem pullOpen_d_apply' (W : V'.Opens) (a : ℕ) (f : (pullOpen p πZ W).cochain K a) (σ : K.Idx (a + 1)) :
    ((pullOpen p πZ W).d K a f σ : Γ(V', W ⊓ (Opens.map p.base).obj (K.inter σ)))
      = ∑ j : Fin (a + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          (V'.presheaf.map (homOfLE (inf_le_inf_left W
            ((Opens.map p.base).monotone (K.inter_le_inter_face σ j)))).op).hom (f (K.face σ j)) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  simp only [OModulePresheaf.d, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

section Rows

variable [IsSeparated πZ] [IsSeparated (p ≫ πZ)]

def rowC_equiv {b : ℕ} (τ : K'.Idx b) (a : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    (pullOpen p πZ (K'.inter τ)).cochain K a ≃ₗ[R] (rowCoverOf p πZ K K' τ).cochain a :=
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  { toFun := fun f σ => (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).le).op).hom (f σ)
    invFun := fun g σ => (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).ge).op).hom (g σ)
    left_inv := fun f => funext fun σ => by
      show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (f σ)) = f σ
      rw [Scheme.TwoAffineOpenCover.res_res]; exact res_self' _ _
    right_inv := fun g => funext fun σ => by
      show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (g σ)) = g σ
      rw [Scheme.TwoAffineOpenCover.res_res]; exact res_self' _ _
    map_add' := fun _ _ => funext fun σ => map_add _ _ _
    map_smul' := fun r f => funext fun σ =>
      (Scheme.OrderedAffineCoverOf.res (p ≫ πZ) (inter_rowCoverOf p πZ K K' τ σ).le).map_smul r (f σ) }

theorem rowC_equiv_apply {b : ℕ} (τ : K'.Idx b) (a : ℕ) (f) (σ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    rowC_equiv p πZ K K' τ a f σ = (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).le).op).hom (f σ) :=
  rfl

theorem rowC_comm {b : ℕ} (τ : K'.Idx b) (a : ℕ) :
    letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
    ∀ f, rowC_equiv p πZ K K' τ (a + 1) ((pullOpen p πZ (K'.inter τ)).d K a f)
      = (rowCoverOf p πZ K K' τ).d (p ≫ πZ) a (rowC_equiv p πZ K K' τ a f) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro f; funext σ
  rw [rowC_equiv_apply, pullOpen_d_apply', Scheme.OrderedAffineCoverOf.d_apply]
  refine (map_sum ((V'.presheaf.map _).hom) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
  show (V'.presheaf.map _).hom (((-1 : ℤ) ^ (j : ℕ)) • (V'.presheaf.map _).hom (f (K.face σ j)))
    = ((-1 : ℤ) ^ (j : ℕ)) • (V'.presheaf.map _).hom ((V'.presheaf.map _).hom (f (K.face σ j)))
  rw [map_zsmul, Scheme.TwoAffineOpenCover.res_res]
  exact (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) (Scheme.TwoAffineOpenCover.res_res _ _ _)).symm

theorem ker_dH_succ_le_range_dH (a b : ℕ) :
    LinearMap.ker ((LerayDblCpx p πZ K K').dH (a + 1) b) ≤ LinearMap.range ((LerayDblCpx p πZ K K').dH a b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro c hc
  have hcτ : ∀ τ, rowC_equiv p πZ K K' τ (a + 1) (biC_uncurry' p πZ K K' (a + 1) b c τ)
      ∈ LinearMap.range ((rowCoverOf p πZ K K' τ).d (p ≫ πZ) a) := fun τ =>
    Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen (p ≫ πZ) _
      (Scheme.OrderedAffineCover.isAffineOpen_inter (p ≫ πZ) K' τ) a
      (LinearMap.mem_ker.mpr <|
        (rowC_comm p πZ K K' τ (a + 1) _).symm.trans <|
          (congrArg _ ((dH_uncurry p πZ K K' (a + 1) b c τ).symm.trans
            ((congrFun (congrArg _ (LinearMap.mem_ker.mp hc)) τ).trans
              (congrFun (map_zero _) τ)))).trans (map_zero _))
  choose g hg using hcτ
  refine ⟨(biC_uncurry' p πZ K K' a b).symm fun τ => (rowC_equiv p πZ K K' τ a).symm (g τ),
    (biC_uncurry' p πZ K K' (a + 1) b).injective (funext fun τ =>
      (dH_uncurry p πZ K K' a b _ τ).trans ((rowC_equiv p πZ K K' τ (a + 1)).injective ?_))⟩
  have hsimp : biC_uncurry' p πZ K K' a b
      ((biC_uncurry' p πZ K K' a b).symm fun τ' => (rowC_equiv p πZ K K' τ' a).symm (g τ')) τ
      = (rowC_equiv p πZ K K' τ a).symm (g τ) :=
    congrFun ((biC_uncurry' p πZ K K' a b).apply_symm_apply _) τ
  rw [rowC_comm, hsimp, LinearEquiv.apply_symm_apply]
  exact hg τ

theorem ker_dH_zero_eq_range_biAug (b : ℕ) :
    LinearMap.ker ((LerayDblCpx p πZ K K').dH 0 b) = LinearMap.range (biAug p πZ K K' b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  have hbridge : ∀ (τ : K'.Idx b) (y : Γ(V', K'.inter τ)),
      rowC_equiv p πZ K K' τ 0 (fun σ =>
          (V'.presheaf.map (homOfLE (inf_le_left : biOpen p K K' 0 b σ τ ≤ K'.inter τ)).op).hom y)
        = (rowCoverOf p πZ K K' τ).aug (p ≫ πZ) y :=
    fun τ y => funext fun σ => by
      show (V'.presheaf.map _).hom ((V'.presheaf.map _).hom y) = (V'.presheaf.map _).hom y
      rw [Scheme.TwoAffineOpenCover.res_res]
  refine le_antisymm (fun c hc => ?_) (fun _ ⟨y, hy⟩ => hy ▸ LinearMap.mem_ker.mpr ?_)
  · choose y hy using fun τ => ((Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug (p ≫ πZ)
        (rowCoverOf p πZ K K' τ)).le
      (LinearMap.mem_ker.mpr <|
        (rowC_comm p πZ K K' τ 0 _).symm.trans <|
          (congrArg _ ((dH_uncurry p πZ K K' 0 b c τ).symm.trans
            ((congrFun (congrArg _ (LinearMap.mem_ker.mp hc)) τ).trans
              (congrFun (map_zero _) τ)))).trans (map_zero _)))
    refine ⟨y, funext fun ⟨σ, τ⟩ => ?_⟩
    have hkey := congrArg (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).ge).op).hom
      (congrFun (hy τ) σ)
    rw [Scheme.OrderedAffineCoverOf.aug_apply, rowC_equiv_apply, Scheme.TwoAffineOpenCover.res_res,
      Scheme.TwoAffineOpenCover.res_res] at hkey
    exact hkey.trans (res_self' _ _)
  · refine (biC_uncurry' p πZ K K' 1 b).injective (funext fun τ => ?_)
    refine (dH_uncurry p πZ K K' 0 b _ τ).trans
      (((rowC_equiv p πZ K K' τ 1).injective ?_).trans (congrFun (map_zero (biC_uncurry' p πZ K K' 1 b)) τ).symm)
    refine (rowC_comm p πZ K K' τ 0 _).trans
      ((congrArg _ (hbridge τ (y τ))).trans ((LinearMap.mem_ker.mp
        ((Scheme.OrderedAffineCoverOf.ker_d_zero_eq_range_aug (p ≫ πZ) _).ge ⟨y τ, rfl⟩)).trans
        (map_zero (rowC_equiv p πZ K K' τ 1)).symm))

theorem biAug_injective (b : ℕ) : Function.Injective (biAug p πZ K K' b) := by
  letI := Scheme.OrderedAffineCoverOf.moduleSections (p ≫ πZ)
  intro y₁ y₂ hy
  refine funext fun τ => Scheme.OrderedAffineCoverOf.aug_injective (p ≫ πZ) (rowCoverOf p πZ K K' τ) (funext fun σ => ?_)
  have key := congrArg (V'.presheaf.map (homOfLE (inter_rowCoverOf p πZ K K' τ σ).le).op).hom (congrFun hy (σ, τ))
  rw [biAug_apply, biAug_apply, Scheme.TwoAffineOpenCover.res_res, Scheme.TwoAffineOpenCover.res_res] at key
  exact key

end Rows

end AlgebraicGeometry.OModulePresheaf.Leray

end

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Leray _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.AlgebraicGeometry.OModulePresheaf.Leray in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Leray _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.AlgebraicGeometry.OModulePresheaf.Leray" in

theorem solution
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ a b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH (a + 1) b)
        ≤ LinearMap.range ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH a b)) ∧
      (∀ b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH 0 b)
        = LinearMap.range (OModulePresheaf.Leray.biAug p πZ K K' b)) ∧
      ∀ b : ℕ, Function.Injective (OModulePresheaf.Leray.biAug p πZ K K' b) :=
  ⟨ker_dH_succ_le_range_dH p πZ K K', ker_dH_zero_eq_range_biAug p πZ K K', biAug_injective p πZ K K'⟩
end S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
