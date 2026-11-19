/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CohCarrier_exists_gamma0_lift_dvd (git blob 9b26d918b225058694df4e09899d67c6bffde11f, sha256 6a0a3d61e4aeb15930b78c113f1c8c2660b3fb407a7bcb021a72baefb2ead9c1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CohCarrier_exists_gamma0_lift_dvd

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, gamma0Units M σ = d ∧ ((ℓ * M : ℕ) : ℤ) ∣ ((σ : SL(2, ℤ)) 1 0) := by
  have hdvd : M ∣ ℓ * M := dvd_mul_left M ℓ
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective hdvd d
  obtain ⟨τ, hτ⟩ := gamma0Units_surjective (ℓ * M) u
  have hτ0 : ((τ : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 (ℓ * M) := τ.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hτ0
  have hσ0 : ((τ : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hdvd) hτ0
  refine ⟨⟨(τ : SL(2, ℤ)), hσ0⟩, ?_, hτ0⟩
  apply Units.ext
  rw [val_gamma0Units, ← hu, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hτ, val_gamma0Units]
  show (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ZMod.castHom hdvd (ZMod M) ((((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (ℓ * M)))
  rw [map_intCast]
