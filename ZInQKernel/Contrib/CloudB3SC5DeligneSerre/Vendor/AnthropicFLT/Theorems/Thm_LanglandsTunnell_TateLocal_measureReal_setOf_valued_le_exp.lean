/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp (git blob 6379803293513a4538c57b472ffddd393469ac65, sha256 28fcee2baeb0ecfc96e86af45b1ed1972f3e63605dc22ef8eeb05568642142d0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  revert K v μ k
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp.solution
