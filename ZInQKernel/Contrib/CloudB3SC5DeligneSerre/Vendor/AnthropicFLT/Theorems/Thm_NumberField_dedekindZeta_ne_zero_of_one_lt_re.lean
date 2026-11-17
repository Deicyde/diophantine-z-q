/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_dedekindZeta_ne_zero_of_one_lt_re (git blob 0babf5bee1c51de3a7f23308ddb39eb9249f1b0d, sha256 0c23e20cd64b149dd44911507f444754b77e2650a17f771e992435db78068ba1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.DedekindZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_dedekindZeta_ne_zero_of_one_lt_re

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem NumberField.dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K]
    [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s ≠ 0 := by
  revert K s hs
  exact @_root_.P2MW.S_NumberField_dedekindZeta_ne_zero_of_one_lt_re.solution
