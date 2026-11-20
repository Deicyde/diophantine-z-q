/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_nonempty_kerBaseChangeTowerEquiv. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_nonempty_kerBaseChangeTowerEquiv

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

theorem TwoChartCech.nonempty_kerBaseChangeTowerEquiv
    {R : Type u} [CommRing R] {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
    (d : C0 →ₗ[R] C1) (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] :
    ∃ e : LinearMap.ker ((d.baseChange S).baseChange T) ≃ₗ[T] LinearMap.ker (d.baseChange T),
      ∀ z, (e z : T ⊗[R] C0) = TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T C0 z := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_nonempty_kerBaseChangeTowerEquiv.solution
