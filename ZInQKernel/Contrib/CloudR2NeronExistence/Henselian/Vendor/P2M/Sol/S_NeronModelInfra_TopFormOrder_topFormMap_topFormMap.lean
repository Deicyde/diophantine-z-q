import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap.lean
Original Git blob: dd738d02b2efca7895a6843a75d7e02366aabdcd
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open NeronModelInfra.TopFormOrder

universe u

namespace BenchOTFMComp
h77_bridge_namespace

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


end P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
