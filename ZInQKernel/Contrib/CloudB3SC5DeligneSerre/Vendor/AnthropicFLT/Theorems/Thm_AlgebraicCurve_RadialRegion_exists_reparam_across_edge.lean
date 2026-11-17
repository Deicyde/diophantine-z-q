/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge (git blob af6baa8a293343e21d1401d7cf02720f23955672, sha256 45a030831dc8263dd7f32ab1b0b8589e61840e2a874f6891d7b3d1862390cb38).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CellDissection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_reparam_across_edge :
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (a b : ℝ), 0 < a → 0 < b →
      R.q.re + a = R'.q.re - b →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / a)⁻¹) →
      (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)) →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.cos t / b)⁻¹) →
      R'.arcIcc k' ⊆ Ioo (π / 2) (3 * π / 2) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) ∧
    (∀ (R R' : RadialRegion) (k : Fin R.N) (k' : Fin R'.N) (c d : ℝ), 0 < c → 0 < d →
      R.q.im + c = R'.q.im - d →
      (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / c)⁻¹) → R.arcIcc k ⊆ Ioo 0 π →
      (∀ t ∈ R'.arcIcc k', R'.r t = (-Real.sin t / d)⁻¹) → R'.arcIcc k' ⊆ Ioo π (2 * π) →
      R.loop (R.φs k.castSucc) = R'.loop (R'.φs k'.succ) →
      R.loop (R.φs k.succ) = R'.loop (R'.φs k'.castSucc) →
      ∃ ψ : ℝ → ℝ, StrictAntiOn ψ (R'.arcIcc k') ∧ ContDiffOn ℝ 1 ψ (R'.arcIcc k') ∧
        ψ (R'.φs k'.castSucc) = R.φs k.succ ∧ ψ (R'.φs k'.succ) = R.φs k.castSucc ∧
        ∀ t ∈ R'.arcIcc k', R'.loop t = R.loop (ψ t)) := @_root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_reparam_across_edge.solution
