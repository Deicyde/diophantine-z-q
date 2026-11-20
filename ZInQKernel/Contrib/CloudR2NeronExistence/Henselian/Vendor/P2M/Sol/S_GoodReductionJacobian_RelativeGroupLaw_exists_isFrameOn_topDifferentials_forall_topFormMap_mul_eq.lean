import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq.lean
Original Git blob: b760ded1d8e021cafab0274e8526c6f7a6d52f77
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g] :
    ∃ ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d, ⊤), Scheme.Modules.IsFrameOn ω ⊤ ∧
      ∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) g)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g)
        (U' U'' : G.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(G, U') F] [Algebra Γ(G, U'') F],
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U''
        ∀ [IsScalarTower K Γ(G, U') F] [IsScalarTower K Γ(G, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U'') F)) ≫ hU''.fromSpec =
          (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(G, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(G, U') F d ω' := by
  obtain ⟨ω, hfr, hω⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq g LG d
  exact ⟨ω, hfr,
    GoodReductionJacobian.RelativeGroupLaw.topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq g LG d ω hω⟩


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
