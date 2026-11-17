/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField (git blob 8acc3ccda42c53fd08c9fad6ff5be4a113ac81e6, sha256 fc1cb7826691b78213ce3ed306b387e278987f424c62cddcf64d3b71b836bef7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ordDiff_zero_of_perfectField

noncomputable section

open AlgebraicCurve

private theorem ordDiff_smul_D_uniformizer {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) (g : F) :
    v.ordDiff (g • KaehlerDifferential.D K F v.uniformizer_alt) = v.ord g := by
  have h1 : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  haveI := Place.isSeparable_adjoin_of_ord_eq_one x v h1
  have hD : KaehlerDifferential.D K F v.uniformizer_alt ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K v.uniformizer_alt
      (v.transcendental_of_ord_ne_zero (h1 ▸ one_ne_zero))
  rw [Place.ordDiff_def, smul_left_injective F hD (Place.diffCoeff_smul_D ⟨g, rfl⟩)]

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) :
    v.ordDiff 0 = 0 := by
  simpa using ordDiff_smul_D_uniformizer x v 0

end
