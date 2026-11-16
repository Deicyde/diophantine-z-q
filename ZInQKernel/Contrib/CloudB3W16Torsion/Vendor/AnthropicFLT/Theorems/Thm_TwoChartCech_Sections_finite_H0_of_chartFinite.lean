/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_TwoChartCech_Sections_finite_H0_of_chartFinite. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_TwoChartCech_Sections_finite_H0_of_chartFinite

set_option backward.isDefEq.respectTransparency false

universe u

theorem TwoChartCech.Sections.finite_H0_of_chartFinite
    {R : Type u} [CommRing R] [IsNoetherianRing R] {𝒰 : TwoChartCech.Cover.{u, u} R}
    (S : TwoChartCech.Sections.{u, u, u} 𝒰)
    (f : 𝒰.A0) (g : 𝒰.A1) (hfg : 𝒰.ρ0 f * 𝒰.ρ1 g = 1)
    (hfin0 : Module.Finite (Algebra.adjoin R ({f} : Set 𝒰.A0)) S.M0)
    (hfin1 : Module.Finite (Algebra.adjoin R ({g} : Set 𝒰.A1)) S.M1)
    (hloc0 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ0 f) ^ n • m ∈ LinearMap.range S.r0)
    (hloc1 : ∀ m : S.M01, ∃ n : ℕ, (𝒰.ρ1 g) ^ n • m ∈ LinearMap.range S.r1)
    (htors0 : ∀ x : S.M0, S.r0 x = 0 → ∃ n : ℕ, f ^ n • x = 0)
    (htors1 : ∀ y : S.M1, S.r1 y = 0 → ∃ n : ℕ, g ^ n • y = 0) :
    Module.Finite R S.H0 := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Sections_finite_H0_of_chartFinite.solution
