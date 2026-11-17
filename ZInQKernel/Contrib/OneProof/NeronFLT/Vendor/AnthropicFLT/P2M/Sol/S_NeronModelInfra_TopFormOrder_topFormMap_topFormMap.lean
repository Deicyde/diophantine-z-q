/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap

set_option autoImplicit false

open NeronModelInfra.TopFormOrder

universe u

namespace BenchOTFMComp

theorem kaehlerMap_kaehlerMap
    (R₁ R₂ R₃ O₁ O₂ O₃ : Type u) [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing O₁] [CommRing O₂] [CommRing O₃]
    [Algebra R₁ R₂] [Algebra R₂ R₃] [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃]
    [Algebra R₁ O₁] [Algebra R₂ O₂] [Algebra R₃ O₃]
    [Algebra O₁ O₂] [Algebra O₂ O₃] [Algebra O₁ O₃] [IsScalarTower O₁ O₂ O₃]
    [Algebra R₁ O₂] [IsScalarTower R₁ O₁ O₂] [IsScalarTower R₁ R₂ O₂]
    [Algebra R₂ O₃] [IsScalarTower R₂ O₂ O₃] [IsScalarTower R₂ R₃ O₃]
    [Algebra R₁ O₃] [IsScalarTower R₁ O₁ O₃] [IsScalarTower R₁ R₃ O₃]
    (x : Ω[O₁⁄R₁]) :
    KaehlerDifferential.map R₂ R₃ O₂ O₃ (KaehlerDifferential.map R₁ R₂ O₁ O₂ x) =
      KaehlerDifferential.map R₁ R₃ O₁ O₃ x := by
  have hx : x ∈ Submodule.span O₁ (Set.range (KaehlerDifferential.D R₁ O₁)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨o, rfl⟩ := hx
      simp only [KaehlerDifferential.map_D]
      rw [← IsScalarTower.algebraMap_apply]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul o x _ hx =>
      rw [LinearMap.map_smul, LinearMap.map_smul, ← hx,
        ← algebraMap_smul O₂ o (KaehlerDifferential.map R₁ R₂ O₁ O₂ x),
        LinearMap.map_smul, algebraMap_smul]

theorem topFormMap_ιMulti (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ) (v : Fin d → Ω[O⁄R']) :
    topFormMap R' K' O F d (exteriorPower.ιMulti O d v) =
      exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (v i)) := by
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti O d v) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end BenchOTFMComp

theorem solution
    (R₁ R₂ R₃ O₁ O₂ O₃ : Type u) [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing O₁] [CommRing O₂] [CommRing O₃]
    [Algebra R₁ R₂] [Algebra R₂ R₃] [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃]
    [Algebra R₁ O₁] [Algebra R₂ O₂] [Algebra R₃ O₃]
    [Algebra O₁ O₂] [Algebra O₂ O₃] [Algebra O₁ O₃] [IsScalarTower O₁ O₂ O₃]
    [Algebra R₁ O₂] [IsScalarTower R₁ O₁ O₂] [IsScalarTower R₁ R₂ O₂]
    [Algebra R₂ O₃] [IsScalarTower R₂ O₂ O₃] [IsScalarTower R₂ R₃ O₃]
    [Algebra R₁ O₃] [IsScalarTower R₁ O₁ O₃] [IsScalarTower R₁ R₃ O₃]
    (d : ℕ) (η : ⋀[O₁]^d (Ω[O₁⁄R₁])) :
    topFormMap R₂ R₃ O₂ O₃ d (topFormMap R₁ R₂ O₁ O₂ d η) = topFormMap R₁ R₃ O₁ O₃ d η := by
  letI i₁₂ := moduleAlong O₁ O₂ (⋀[O₂]^d (Ω[O₂⁄R₂]))
  letI i₂₃ := moduleAlong O₂ O₃ (⋀[O₃]^d (Ω[O₃⁄R₃]))
  letI i₁₃ := moduleAlong O₁ O₃ (⋀[O₃]^d (Ω[O₃⁄R₃]))
  have hη : η ∈ Submodule.span O₁ (Set.range (exteriorPower.ιMulti O₁ d (M := Ω[O₁⁄R₁]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [BenchOTFMComp.topFormMap_ιMulti, BenchOTFMComp.topFormMap_ιMulti,
        BenchOTFMComp.topFormMap_ιMulti]
      congr 1
      funext i
      exact BenchOTFMComp.kaehlerMap_kaehlerMap R₁ R₂ R₃ O₁ O₂ O₃ (v i)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul o x _ hx =>
      rw [LinearMap.map_smul, LinearMap.map_smul]
      change topFormMap R₂ R₃ O₂ O₃ d (algebraMap O₁ O₂ o • topFormMap R₁ R₂ O₁ O₂ d x) =
        algebraMap O₁ O₃ o • topFormMap R₁ R₃ O₁ O₃ d x
      rw [LinearMap.map_smul, hx]
      change algebraMap O₂ O₃ (algebraMap O₁ O₂ o) • topFormMap R₁ R₃ O₁ O₃ d x = _
      rw [← IsScalarTower.algebraMap_apply]
