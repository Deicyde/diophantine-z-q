import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints.lean
Original Git blob: 7aea691de198b5d6d442cb2a74bc0820f8a75865
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 1 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} [IsSeparated gK]
    (M : ModelFamily R K gK) (hM : ∀ i, LocallyOfFiniteType (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ) :
    ∃ (i : M.ι) (U : Z.Opens) (_ : ζ ∈ U) (u : SchemeHomOver (U.ι ≫ z) (M.str i)),
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K (M.str i) (U.ι ≫ z) u) (M.chart i)).1 =
        pullback.map (U.ι ≫ z) (specGenericFibreInclusion R K) z (specGenericFibreInclusion R K) U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
