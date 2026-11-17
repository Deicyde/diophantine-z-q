/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PeriodPair_weierstrassP_scale (git blob 0cc12e678f7b1c3d3e8ec4e28a37cc657fc60405, sha256 e48adb11e51761e36ff494661aa94964443731238fde826e547aa2df83acd2d4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PeriodPair_weierstrassP_scale

set_option autoImplicit false

noncomputable section

open PeriodPair

theorem solution (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    (L.scale α).weierstrassP ((α : ℂ) * z) = ((α : ℂ) ^ 2)⁻¹ * L.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP,
    ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (α : ℂ) * z - ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) =
      α * (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) by ring,
    show ((p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂)) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_pow, one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_sub]
