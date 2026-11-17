/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_kerMap_injective_of_H0_eq_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_kerMap_injective_of_H0_eq_zero

set_option backward.isDefEq.respectTransparency false

universe u

theorem TwoChartCech.kerMap_injective_of_H0_eq_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {K0 K1 E0 E1 S0 S1 : Type u}
    [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
    [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
    [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
    (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
    (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
    (hp0 : Function.Surjective p0) (hp1 : Function.Surjective p1)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1)
    (hE : LinearMap.ker dE = ⊥) [Module.Finite R (K1 ⧸ LinearMap.range dK)] :
    Module.Finite R (LinearMap.ker dS) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_kerMap_injective_of_H0_eq_zero.solution
