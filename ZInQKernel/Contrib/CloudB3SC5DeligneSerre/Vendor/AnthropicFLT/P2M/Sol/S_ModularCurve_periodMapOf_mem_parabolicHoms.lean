/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_periodMapOf_mem_parabolicHoms (git blob addafb95f39b7ff9f0c7e7a0a1c87682df59caec, sha256 08ac30658d00eed23e0be9aa3a8f098a477adb2b5d30aa5dd54eb11ac5d3f225).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_periodMapOf_mem_parabolicHoms

set_option autoImplicit false

open scoped MatrixGroups
open UpperHalfPlane Filter Topology

namespace ModularCurve
export _root_.ModularCurve (HasEquivariantPrimitiveOf periodMapOf periodMapOf_def period Period.parabolicHoms)
namespace PeriodMapParabolicOf
open _root_.ModularCurve

open ModularCurve.Period

theorem tendsto_vadd_atImInfty (x : ℝ) :
    Tendsto (fun z : ℍ => x +ᵥ z) atImInfty atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  exact tendsto_comap.congr fun z => (vadd_im x z).symm

theorem const_eq_zero_of_tendsto_sub {α : Type*} {l : Filter α} [l.NeBot]
    {g h : α → ℂ} {L c : ℂ} (hg : Tendsto g l (𝓝 L)) (hh : Tendsto h l (𝓝 L))
    (hc : ∀ a, g a - h a = c) : c = 0 := by
  have hsub : Tendsto (fun a => g a - h a) l (𝓝 (L - L)) := hg.sub hh
  rw [sub_self] at hsub
  exact tendsto_nhds_unique (tendsto_const_nhds.congr fun a => (hc a).symm) hsub

theorem period_eq_zero {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}
    (hF : IsEquivariantPrimitive Γ F) (δ : SL(2, ℤ)) {L : ℂ}
    (hlim : Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)) (n : ℤ) (ε : SL(2, ℤ))
    (hε : ε = 1 ∨ ε = -1) (hγ : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ) :
    hF.period ⟨_, hγ⟩ = 0 := by

  have hεact : ∀ z : ℍ, (ε : SL(2, ℤ)) • z = z := by
    intro z
    rcases hε with rfl | rfl
    · exact one_smul _ z
    · ext1
      rw [UpperHalfPlane.specialLinearGroup_apply]
      simp
  have hkey : ∀ w : ℍ, (ε * (δ * ModularGroup.T ^ n * δ⁻¹) : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • w)
      = δ • (ModularGroup.T ^ n • w) := by
    intro w
    rw [mul_smul, hεact, ← mul_smul, ← mul_smul]
    congr 1
    group
  have hc' : ∀ w : ℍ, F (δ • (ModularGroup.T ^ n • w)) - F (δ • w) = hF.period ⟨_, hγ⟩ := by
    intro w
    rw [← hkey]
    exact hF.sub_eq_period ⟨_, hγ⟩ (δ • w)
  refine const_eq_zero_of_tendsto_sub
    (g := fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
    (h := fun w : ℍ => F (δ • w)) (L := L) ?_ hlim hc'
  have hfun : (fun w : ℍ => F (δ • (ModularGroup.T ^ n • w)))
      = (fun w : ℍ => F (δ • w)) ∘ fun w : ℍ => ((n : ℤ) : ℝ) +ᵥ w := by
    funext w
    simp only [Function.comp_apply, UpperHalfPlane.modular_T_zpow_smul]
  rw [hfun]
  exact hlim.comp (tendsto_vadd_atImInfty ((n : ℤ) : ℝ))

theorem isParabolicHom_periodHom {Γ : Subgroup SL(2, ℤ)} {f : CuspForm Γ 2} {F : ℍ → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) :
    IsParabolicHom Γ hF.2.2.1.periodHom := by
  intro γ hγ
  obtain ⟨ε, δ, n, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
  obtain ⟨L, hL⟩ := hF.2.2.2 δ
  have hmem : ε * (δ * ModularGroup.T ^ n * δ⁻¹) ∈ Γ := by rw [← hγeq]; exact γ.2
  have hγ' : γ = ⟨_, hmem⟩ := Subtype.ext hγeq
  rw [IsEquivariantPrimitive.periodHom_apply, hγ']
  exact period_eq_zero hF.2.2.1 δ hL n ε hε hmem

theorem main (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ parabolicHoms ℂ Γ ℂ := by
  classical
  by_cases h : ∃ F : ℍ → ℂ, ModularCurve.HasEquivariantPrimitiveOf Γ f F
  · obtain ⟨F, hF⟩ := h
    obtain ⟨F₀, h₀, hp⟩ := ModularCurve.periodMapOf_def Γ f hF
    rw [hp]
    exact isParabolicHom_periodHom h₀
  · have : ModularCurve.periodMapOf Γ f = 0 := dif_neg h
    rw [this]
    exact Submodule.zero_mem _

end ModularCurve.PeriodMapParabolicOf

theorem solution (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2) :
    ModularCurve.periodMapOf Γ f ∈ ModularCurve.Period.parabolicHoms ℂ Γ ℂ :=
  ModularCurve.PeriodMapParabolicOf.main Γ f
