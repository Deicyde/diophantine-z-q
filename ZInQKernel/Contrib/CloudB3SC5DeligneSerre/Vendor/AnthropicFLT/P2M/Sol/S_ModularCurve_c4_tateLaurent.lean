/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_c4_tateLaurent (git blob 68c0eaa60b83b100b7de3c0431f7c920dd8e64e8, sha256 6f63cccec55ba2037e79439cadd81a8efc85bd8787545a053bcf3f384426c3a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateFormal
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace PowerSeries
end PowerSeries
namespace HahnSeries
end HahnSeries
namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_c4_tateLaurent.ModularCurve
end P2MW.S_ModularCurve_c4_tateLaurent.ModularCurve

namespace P2MW.S_ModularCurve_c4_tateLaurent

set_option autoImplicit false

open _root_.PowerSeries
open _root_.HahnSeries
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_c4_tateLaurent.ModularCurve

namespace ModularCurve
export _root_.ModularCurve (tateA4 coeff_tateA4 tatePowerSeries tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ tatePowerSeries_a₄ laurentOfInt_apply tateLaurent eisenstein4)
namespace TD1
open _root_.ModularCurve

theorem c₄_tatePowerSeries : tatePowerSeries.c₄ = 1 - 48 * tateA4 := by
  rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁, tatePowerSeries_a₂,
    tatePowerSeries_a₃, tatePowerSeries_a₄]
  ring

theorem one_sub_48_tateA4 : (1 - 48 * tateA4 : PowerSeries ℤ) = eisenstein4 := by
  ext n
  have h48 : (48 : PowerSeries ℤ) * tateA4 = (48 : ℕ) • tateA4 := by
    rw [nsmul_eq_mul, Nat.cast_ofNat]
  rw [map_sub, PowerSeries.coeff_one, eisenstein4, PowerSeries.coeff_mk, h48, map_nsmul, coeff_tateA4,
    nsmul_eq_mul, Nat.cast_ofNat]
  split_ifs with h
  · subst h; simp
  · simp only [zero_sub, mul_neg, neg_neg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring

theorem main (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by
  rw [tateLaurent, WeierstrassCurve.map_c₄, c₄_tatePowerSeries, one_sub_48_tateA4, laurentOfInt_apply]

end ModularCurve.TD1

open PowerSeries HahnSeries in
theorem solution (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) :=
  ModularCurve.TD1.main K
