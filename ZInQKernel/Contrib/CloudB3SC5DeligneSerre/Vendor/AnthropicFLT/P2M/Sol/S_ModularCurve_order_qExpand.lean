/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_order_qExpand (git blob dfdb8550d116a7acd2d5c79bf127f4e762869bde, sha256 c9eb7decbedb24f207591c304840bd3c8055a652c3ed855a3b8b9c9a8d3f3563).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_order_qExpand

open ModularCurve

theorem solution {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) : (qExpand R N f).order = N * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have hc : (qExpand R N f).coeff ((N : ℤ) * f.order) ≠ 0 := by
    rw [qExpand_coeff_mul]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand R N f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  by_cases hdvd : (N : ℤ) ∣ (qExpand R N f).order
  · obtain ⟨m, hm⟩ := hdvd
    rw [hm, qExpand_coeff_mul] at hk
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmlt : m < f.order := by
      rw [hm] at hlt
      exact lt_of_mul_lt_mul_left hlt hNpos.le
    exact hk (HahnSeries.coeff_eq_zero_of_lt_order hmlt)
  · exact hk (qExpand_coeff_of_not_dvd N f hdvd)
