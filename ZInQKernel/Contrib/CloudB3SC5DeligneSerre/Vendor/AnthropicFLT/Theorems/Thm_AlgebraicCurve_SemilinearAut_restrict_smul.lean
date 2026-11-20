/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul (git blob c9fb4c094cfdecb285ba1c4a0ef9ed3751b46b02, sha256 4432f0516b511619105fa044e2cbf8a14195bc2f6495e3d2f34ef1c400c2dd5f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_SemilinearAut_restrict_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut
theorem AlgebraicCurve.SemilinearAut.restrict_smul {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') : (g' • w).restrict F = g • (w.restrict F) := by
  revert K F F' g g' hgg' w
  exact @_root_.P2MW.S_AlgebraicCurve_SemilinearAut_restrict_smul.solution
