import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing.lean
Original Git blob: 80047361c1371320ecad220e62b8c266650037f3
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Smooth.exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ X)
    (hx₀ : x₀ ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) ≫ s = x₀ := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_AlgebraicGeometry_Smooth_exists_comp_eq_id_and_specMap_comp_eq_of_henselianLocalRing.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
