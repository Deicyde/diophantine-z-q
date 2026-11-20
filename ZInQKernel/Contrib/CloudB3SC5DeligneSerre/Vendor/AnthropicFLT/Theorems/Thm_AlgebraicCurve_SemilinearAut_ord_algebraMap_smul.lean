/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul (git blob e91c0b1f7fa80531cb90623b4641d34dcadd4153, sha256 a0e37081d2718af5671601d64a416b3bb5e802f3b3ff8de5f34a605961406b83).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.ord_algebraMap_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) : (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f)) := by
  revert K F F' g g' hgg' w f
  exact @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_ord_algebraMap_smul.solution
