/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental (git blob e4d159cd1c196b14a90de500ec9f69c9f89e1f59, sha256 85cc18fee132a49fa546fbcacca0005c35229c6b2dd1ae0e507c5557ef13ec9a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem IsIntegral.mem_span_of_adjoin_simple_constants_transcendental {K : Type*}
    [Field K] [Algebra ℂ K]
    (F : IntermediateField ℚ ℂ) (t : K) (ht : Transcendental ℂ t)
    (S : Set K) (htS : t ∈ S) (hSfin : S.Finite)
    (hSint : ∀ s ∈ S, IsIntegral
      ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) s)
    (c : ℂ) (hc : Transcendental ↥F c)
    (htc : Transcendental ↥(Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S))
      (algebraMap ℂ K c))
    (y : K)
    (hyS : y ∈ Subfield.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ S))
    (hyB : IsIntegral ↥(Subring.closure
      (⇑(algebraMap ℂ K) '' (IntermediateField.adjoin ↥F {c} : Set ℂ) ∪ {t})) y) :
    y ∈ Submodule.span ℂ {z : K | z ∈ Subfield.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ S) ∧
      IsIntegral ↥(Subring.closure (⇑(algebraMap ℂ K) '' (F : Set ℂ) ∪ {t})) z} := by
  revert K F t ht S htS hSfin hSint c hc htc y hyS hyB
  exact @_root_.P2MW.S_IsIntegral_mem_span_of_adjoin_simple_constants_transcendental.solution
