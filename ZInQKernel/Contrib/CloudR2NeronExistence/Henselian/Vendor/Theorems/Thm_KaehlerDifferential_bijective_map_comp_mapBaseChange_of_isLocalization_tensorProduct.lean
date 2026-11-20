import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct.lean
Original Git blob: e16b6672009c706d23f30e1d7c850faa3633a757
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct

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

open TensorProduct

theorem KaehlerDifferential.bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct
    (R A A' B C : Type u) [CommRing R] [CommRing A] [CommRing A'] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    [Algebra R C] [Algebra A C] [Algebra A' C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [IsScalarTower A A' C] [IsScalarTower R A' C]
    (M : Submonoid A) [IsLocalization M A']
    [Algebra (A ⊗[R] B) C] [IsScalarTower A (A ⊗[R] B) C]
    (hB : (algebraMap (A ⊗[R] B) C).comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (N : Submonoid (A ⊗[R] B)) [IsLocalization N C] :
    Function.Bijective
      ((KaehlerDifferential.map R A' C C).restrictScalars C ∘ₗ KaehlerDifferential.mapBaseChange R B C) := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_KaehlerDifferential_bijective_map_comp_mapBaseChange_of_isLocalization_tensorProduct.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
