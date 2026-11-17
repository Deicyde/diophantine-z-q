/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps (git blob 1e40c599f8952565c7bbfada720b6e9f3f4ef03d, sha256 7e6c5e23e73c67359b6f87711c51bc60f430a2117ebbb9ca782340f1926911b4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_pow_pullback_laps (R : RadialRegion) (hN : 2 ≤ R.N) (e : ℕ) (he : e ≠ 0) :
    ∃ R' : RadialRegion,
      R'.q = 0 ∧ R'.N = e * R.N ∧
      (∀ u : ℂ, u ∈ R'.K ↔ R.q + u ^ e ∈ R.K) ∧
      (∀ u : ℂ, u ∈ R'.Kint ↔ R.q + u ^ e ∈ R.Kint) ∧
      (∀ ψ : ℝ, R.q + R'.loop ψ ^ e = R.loop ((e : ℝ) * ψ)) ∧
      ∃ lap : Fin e → Fin R.N → Fin R'.N,
        Function.Bijective (fun jk : Fin e × Fin R.N => lap jk.1 jk.2) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          R'.arcIcc (lap j k) = (fun t : ℝ => (2 * π * ((j : ℕ) : ℝ) + t) / (e : ℝ)) '' R.arcIcc k) ∧
        (∀ (j : Fin e) (k : Fin R.N),
          (fun u : ℂ => R.q + u ^ e) '' R'.arcSet (lap j k) = R.arcSet k) ∧
        (∀ (j : Fin e) (k : Fin R.N), Set.InjOn (fun u : ℂ => R.q + u ^ e) (R'.arcSet (lap j k))) ∧
        (∀ k : Fin R.N, ∃ U : Fin e → Set ℂ, (∀ j, IsOpen (U j)) ∧
          Pairwise (fun j j' => Disjoint (U j) (U j')) ∧ ∀ j, R'.arcSet (lap j k) ⊆ U j) := by
  revert R hN e he
  exact @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_pow_pullback_laps.solution
