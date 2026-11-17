/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Dimension.Finrank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

theorem TwoChartCech.finrank_ker_baseChange_eq_of_field_extension
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (K L : Type u) [Field K] [Field L] [Algebra R K] [Algebra R L] [Algebra K L]
    [IsScalarTower R K L] :
    Module.finrank K (LinearMap.ker (d.baseChange K)) = Module.finrank L (LinearMap.ker (d.baseChange L)) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_finrank_ker_baseChange_eq_of_field_extension.solution
