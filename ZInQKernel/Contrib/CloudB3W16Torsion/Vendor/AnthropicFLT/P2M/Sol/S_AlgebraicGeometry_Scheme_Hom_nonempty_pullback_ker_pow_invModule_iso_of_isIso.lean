/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.IdealSheafData.one_eq_top Scheme.IdealSheafData.le_map_comap Scheme.Modules.pullback Scheme.Hom Scheme.IdealSheafData.map_ker Scheme.IdealSheafData.map_id Scheme Scheme.IdealSheafData.comap_top IsClosedImmersion Scheme.IdealSheafData.map_comp Scheme.IdealSheafData.map_mono Scheme.Modules Scheme.IdealSheafData.comap_map_le Scheme.IdealSheafData Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison)
namespace BCKerGlue
open AlgebraicGeometry

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comap_eq_map_inv {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (J : X.IdealSheafData) :
    J.comap f = J.map (inv f) := by
  apply le_antisymm
  · have h : ((J.map (inv f)).map f).comap f ≤ J.map (inv f) :=
      Scheme.IdealSheafData.comap_map_le (J.map (inv f)) f
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.map_id] at h
  · have h : J.map (inv f) ≤ ((J.comap f).map f).map (inv f) :=
      Scheme.IdealSheafData.map_mono (inv f) (Scheme.IdealSheafData.le_map_comap J f)
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem ker_comap_eq_ker {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) (p' : T ⟶ Y)
    (hp : p' ≫ f = p) : p.ker.comap f = p'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← hp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem comap_pow {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

end AlgebraicGeometry.BCKerGlue

open AlgebraicGeometry.BCKerGlue in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {X Y T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) [IsClosedImmersion p] (p' : T ⟶ Y)
    (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) (n : ℕ) :
    Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).invModule) ≅ ((p'.ker) ^ n).invModule) ∧
      Nonempty ((Scheme.Modules.pullback f).obj ((p.ker ^ n).module) ≅ ((p'.ker) ^ n).module) := by

  have hk : (p.ker ^ n).comap f = p'.ker ^ n := by
    rw [comap_pow, ker_comap_eq_ker f p p' hp]
  have hIn : (p.ker ^ n).IsInvertible := hI.pow n
  have hIn' : ((p.ker ^ n).comap f).IsInvertible := by
    rw [hk]
    exact hI'.pow n
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso f hIn hIn'
    exact ⟨e ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hk)⟩
  · have h := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f hIn hIn'
    exact ⟨@asIso _ _ _ _ ((p.ker ^ n).pullbackModuleComparison f) h ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hk)⟩
