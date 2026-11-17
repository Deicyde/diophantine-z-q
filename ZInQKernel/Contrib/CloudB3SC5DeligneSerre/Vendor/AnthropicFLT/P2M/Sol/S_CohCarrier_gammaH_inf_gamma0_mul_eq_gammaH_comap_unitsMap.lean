/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap (git blob 1ea0ea67384fef6f4cb7626f1cee749ba4fb5e21, sha256 38a30fa2e643752e6b62501f67af0c006e1376962fe1a1f774c091de2bdfba93).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M ℓ : ℕ) [NeZero M] [NeZero ℓ]
    (H : Subgroup (ZMod M)ˣ) :
    CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) =
      CohCarrier.GammaH (M * ℓ) (H.comap (ZMod.unitsMap (dvd_mul_right M ℓ))) := by
  ext A
  rw [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, CohCarrier.mem_GammaH_iff]
  constructor
  · rintro ⟨⟨hA0, hH⟩, hA0'⟩
    refine ⟨hA0', ?_⟩
    rw [Subgroup.mem_comap]
    convert hH using 1
    rw [Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ))) = ((A 1 1 : ℤ) : ZMod M)
    rw [ZMod.cast_intCast (dvd_mul_right M ℓ)]
  · rintro ⟨hA0', hH⟩
    have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := by
      have h := CongruenceSubgroup.Gamma0_mem.mp hA0'
      rw [CongruenceSubgroup.Gamma0_mem]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h ⊢
      exact (Int.natCast_dvd_natCast.mpr (dvd_mul_right M ℓ)).trans h
    refine ⟨⟨hA0, ?_⟩, hA0'⟩
    rw [Subgroup.mem_comap] at hH
    convert hH using 1
    rw [Units.ext_iff, ZMod.unitsMap_val, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ)))
    rw [ZMod.cast_intCast (dvd_mul_right M ℓ)]
