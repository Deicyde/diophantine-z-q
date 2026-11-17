/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo (git blob bcd5afbbb0574d61363eeb49ca90655c4bc5ebed, sha256 e725a01767ec5704e1ec616613ac9536058637a4cbb73d6b854b042da0dc52e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.AdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo (K : Type*) [Field K]
    [NumberField K] :
    SecondCountableTopology
      (Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)) := by
  revert K
  exact @_root_.P2MW.S_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo.solution
