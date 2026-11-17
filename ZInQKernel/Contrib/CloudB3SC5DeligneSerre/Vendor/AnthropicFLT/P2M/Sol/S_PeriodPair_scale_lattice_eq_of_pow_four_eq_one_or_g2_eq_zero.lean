/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero (git blob ef86bb10951b2ee9f4644a830f10cdfe99938957, sha256 feb2b31f69cf9b000fedf3cc09e26abd61da7ed1163f22728651d7689cb468c7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace PeriodPair
end PeriodPair
namespace P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.PeriodPair
end P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.PeriodPair

namespace P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero

set_option autoImplicit false

noncomputable section

namespace PeriodPair
export _root_.PeriodPair (lattice ω₁ latticeEquivProd g₃ ω₂ latticeEquiv_symm_apply G g₂ scale scale_ω₁ scale_ω₂ lattice_eq_of_g2_eq_of_g3_eq)
namespace ScaleUnits
open _root_.PeriodPair

open _root_.PeriodPair
open _root_.P2MW.S_PeriodPair_scale_lattice_eq_of_pow_four_eq_one_or_g2_eq_zero.PeriodPair

theorem G_scale (L : PeriodPair) (α : ℂˣ) (k : ℕ) :
    (L.scale α).G k = ((α : ℂ) ^ k)⁻¹ * L.G k := by
  rw [PeriodPair.G, PeriodPair.G, ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_inv]

theorem g₂_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_scale]; ring

theorem g₃_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_scale]; ring

end PeriodPair.ScaleUnits

open PeriodPair.ScaleUnits in
theorem solution (L : PeriodPair) (α : ℂˣ)
    (h₂ : (α : ℂ) ^ 4 = 1 ∨ L.g₂ = 0) (h₃ : (α : ℂ) ^ 6 = 1 ∨ L.g₃ = 0) :
    (L.scale α).lattice = L.lattice := by
  apply PeriodPair.lattice_eq_of_g2_eq_of_g3_eq
  · rw [g₂_scale]
    rcases h₂ with h | h
    · rw [h, inv_one, one_mul]
    · rw [h, mul_zero]
  · rw [g₃_scale]
    rcases h₃ with h | h
    · rw [h, inv_one, one_mul]
    · rw [h, mul_zero]
