/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H1
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H1) ∧
    Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] LinearMap.ker ((𝒱.sectionsOf c M).cechDiff.baseChange A)) ∧
    (Module.Flat R A →
      Nonempty (((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
        ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).H0
      ≃ₗ[A] A ⊗[R] (𝒱.sectionsOf c M).H0)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_cech_sectionsOf_baseChange_equiv_of_locallyTrivial.solution
