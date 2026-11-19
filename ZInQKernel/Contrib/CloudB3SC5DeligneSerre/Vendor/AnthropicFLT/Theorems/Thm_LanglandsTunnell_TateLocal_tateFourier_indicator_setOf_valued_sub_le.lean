/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le (git blob 83aefd447b5c8b5d8a5a4ae28eb5e06c7234afb3, sha256 cae88219d5fbba956c932df7f3edb0bab771eda5d6940cf1b51ab6af225014df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.tateFourier_indicator_setOf_valued_sub_le (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (a : v.adicCompletion K) (m : ℤ) (y : v.adicCompletion K) :
    tateFourier ψ μ ({x : v.adicCompletion K | Valued.v (x - a) ≤ WithZero.exp (-m)}.indicator fun _ => (1 : ℂ)) y
      = ψ (a * y) * ((μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp (-m)} : ℝ) : ℂ)
          * {y' : v.adicCompletion K | Valued.v y' ≤ WithZero.exp (n + m)}.indicator (fun _ => (1 : ℂ)) y := by
  revert K v μ ψ n hψn hψn' a m y
  exact @_root_.P2MW.S_LanglandsTunnell_TateLocal_tateFourier_indicator_setOf_valued_sub_le.solution
