/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

open scoped CategoryTheory.MonObj

namespace P2mThetaFin

variable {X : Scheme.{u}}

lemma pullbackSection_zero {X' : Scheme.{u}} (F : X' ⟶ X) (M : X.Modules) :
    Scheme.Modules.pullbackSectionFLT F (0 : 𝟙_ X.Modules ⟶ M) = 0 := by
  have h : (Scheme.Modules.pullback F).map (0 : (𝟙_ X.Modules) ⟶ M) = 0 := Functor.map_zero _ _ _
  exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·) h).trans comp_zero

end P2mThetaFin

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [IsIntegral X] [GrpObj (Over.mk t)] (hsm : Smooth t) :
    ∃ (L : X.Modules) (_ : Scheme.Modules.IsInvertible L) (θ : 𝟙_ X.Modules ⟶ L), θ ≠ 0 ∧
      Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSectionFLT z.left θ = 0 ↔ Scheme.Modules.pullbackSectionFLT (z * x).left θ = 0} := by

  set e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := 1 with he_def
  obtain ⟨_, ⟨U, hU, rfl⟩, heU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((e.left : Spec (CommRingCat.of k) ⟶ X) (IsLocalRing.closedPoint k))) isOpen_univ

  obtain ⟨L, hL, θ, hθ⟩ :=
    Scheme.Modules.exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen k t U hU
  refine ⟨L, hL, θ, ?_, ?_⟩
  ·
    rintro rfl
    exact ((hθ k e.left).1 (P2mThetaFin.pullbackSection_zero _ L)) heU
  ·
    have hfin :=
      Scheme.finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen k t
        ((U : Set X)ᶜ) U.isOpen.isClosed_compl U hU (by rw [compl_compl]) (fun h => h heU)
    have hset : {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
          Scheme.Modules.pullbackSectionFLT z.left θ = 0 ↔
            Scheme.Modules.pullbackSectionFLT (z * x).left θ = 0} =
        {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
          ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
            z.left (IsLocalRing.closedPoint k) ∈ (U : Set X)ᶜ ↔
              (z * x).left (IsLocalRing.closedPoint k) ∈ (U : Set X)ᶜ} := by
      ext x
      refine forall_congr' fun z => ?_
      exact iff_congr (hθ k z.left) (hθ k (z * x).left)
    rw [hset]
    exact hfin
