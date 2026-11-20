import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq.lean
Original Git blob: 3b2dfe479ecbeb4d9779c646bbae9783c9792304
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
open scoped _root_.TensorProduct
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (d : ℕ) (b : Module.Basis (Fin d) O₀ (Ω[O₀⁄R]))
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    (hρ : (letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
      topFormMap R' K' O F d (exteriorPower.ιMulti O d
        (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i))))) ≠ 0)
    (a : F₀) (ha : a ≠ 0) :
    letI := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
    letI := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
    ord R' K' O d F (topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b))) =
      ord R K O₀ d F₀ (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
