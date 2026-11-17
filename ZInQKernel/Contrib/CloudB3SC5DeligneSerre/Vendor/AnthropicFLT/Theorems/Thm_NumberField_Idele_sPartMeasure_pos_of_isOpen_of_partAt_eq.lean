/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq (git blob a248626230fe0b6cc6dce8041c3be628d3cd2056, sha256 abbe3e76af87788bb83d78e00857bd2e4557c3de819ced70bcec347c885e5b68).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_IdeleProductMeasure
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.Idele IsDedekindDomain
open scoped ENNReal

theorem NumberField.Idele.sPartMeasure_pos_of_isOpen_of_partAt_eq
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t₀ : AdeleRing (𝓞 F) F)).2 v = 1)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsOpen U) (hU₀ : t₀ ∈ U) :
    0 < sPartMeasure F S U := by
  revert F S t₀ ht₀ U hU hU₀
  exact @_root_.P2MW.S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq.solution
