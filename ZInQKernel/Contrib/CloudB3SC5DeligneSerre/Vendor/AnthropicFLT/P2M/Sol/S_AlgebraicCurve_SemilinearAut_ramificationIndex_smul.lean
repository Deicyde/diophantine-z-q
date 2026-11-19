/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul (git blob c45f1ad2987d81977981d8686dc57d17d67edd39, sha256 1bc8b7e1e554ba6aa463b0af60e305048f6a7ccf5d6026fc7bbca3d47978c4e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_ramificationIndex_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).ramificationIndex F = w.ramificationIndex F := by
  unfold Place.ramificationIndex
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hford⟩
    exact ⟨g⁻¹ • f, by rwa [ne_eq, smul_eq_zero_iff_eq], by rw [← ord_algebraMap_smul hgg', hford]⟩
  · rintro ⟨f, hf, hford⟩
    refine ⟨g • f, by rwa [ne_eq, smul_eq_zero_iff_eq], ?_⟩
    rw [ord_algebraMap_smul hgg', inv_smul_smul, hford]

end
