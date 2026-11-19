/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_tsum_lambertTerm_eq (git blob 9f6f05d8e239522fbcc63f7d03979f548798ac48, sha256 f8d53636f40017aedffd7da96ef626c0c9e0c5f4c5e9cac2e54f73abcf3dccfa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateFormal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_tsum_lambertTerm_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
theorem ModularCurve.tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n : ℕ, ((c n : ℕ) : LaurentSeries K) *
        ((HahnSeries.single (p : ℤ) (1 : K)) ^ n / (1 - (HahnSeries.single (p : ℤ) (1 : K)) ^ n)) =
      qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) := by
  revert K p c
  exact @_root_.P2MW.S_ModularCurve_tsum_lambertTerm_eq.solution
