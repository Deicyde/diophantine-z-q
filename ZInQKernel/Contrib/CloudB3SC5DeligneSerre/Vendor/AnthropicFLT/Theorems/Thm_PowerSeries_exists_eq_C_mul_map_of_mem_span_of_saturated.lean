/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated (git blob 5c2a297df5dd11007cb4209c685f7c0b1d4fded9, sha256 bb50da25618360ad53106bf1d28333b6ab05a03edb3161038f6ad75f00f955ca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated
    {L : Type*} [Field L] (A : ValuationSubring L)
    (N : AddSubgroup (PowerSeries ℤ))
    (hN : ∀ (n : ℤ) (p : PowerSeries ℤ), n ≠ 0 → n • p ∈ N → p ∈ N)
    {V : PowerSeries L}
    (hV : V ∈ Submodule.span L
      ((fun p : PowerSeries ℤ => p.map (Int.castRingHom L)) '' (N : Set (PowerSeries ℤ))))
    (hV0 : V ≠ 0) :
    ∃ (c : L) (u : PowerSeries A), c ≠ 0 ∧
      V = PowerSeries.C c * u.map (A.subtype : A →+* L) ∧
      u.map (IsLocalRing.residue A) ≠ 0 ∧
      u.map (IsLocalRing.residue A) ∈
        Submodule.span (IsLocalRing.ResidueField A)
          ((fun p : PowerSeries ℤ => p.map (Int.castRingHom (IsLocalRing.ResidueField A))) ''
            (N : Set (PowerSeries ℤ))) := by
  revert L A N hN V hV hV0
  exact @_root_.P2MW.S_PowerSeries_exists_eq_C_mul_map_of_mem_span_of_saturated.solution
