import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.lean
Original Git blob: 12ceb1c024f372e6e5b2272a96e8dd68542c0342
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 2 old-version global performance-guard attribute lines (no proof or type).
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq

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

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g] :
    ∃ ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d, ⊤), Scheme.Modules.IsFrameOn ω ⊤ ∧
      ∀ (V U' U'' : G.Opens) (hV : IsAffineOpen V) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        (W : (pullback g g).Opens) (hW : IsAffineOpen W)
        (hWV : W ≤ pullback.fst g g ⁻¹ᵁ V) (hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U')
        (hWU'' : W ≤ (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1 ⁻¹ᵁ U''),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) V; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U''
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra (pullback.fst g g ≫ g)) W
        letI : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
        letI : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W hWU').hom.toAlgebra
        letI : Algebra Γ(G, U'') Γ(pullback g g, W) :=
          ((LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1.appLE U'' W hWU'').hom.toAlgebra
        ∀ [IsScalarTower K Γ(G, V) Γ(pullback g g, W)] [IsScalarTower K Γ(G, U') Γ(pullback g g, W)]
          [IsScalarTower K Γ(G, U'') Γ(pullback g g, W)],
        ∀ (ω' : ⋀[Γ(G, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'' =
            TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω' := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isFrameOn_topDifferentials_forall_topFormMap_appLE_mul_eq.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
