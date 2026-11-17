/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Finrank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hint : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (hfin : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      Module.Finite L (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange L)))
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one.solution
