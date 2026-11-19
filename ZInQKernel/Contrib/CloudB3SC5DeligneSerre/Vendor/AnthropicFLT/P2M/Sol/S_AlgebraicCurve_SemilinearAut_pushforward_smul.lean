/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_SemilinearAut_pushforward_smul (git blob 9c76aa8b440d934a163fafb2a516a3548b6f0747, sha256 52b83d79adb0deaf75c8d95e7acd07b085fe39b80d53a00417ae03865e788f59).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_restrict_smul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_inertiaDeg_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pushforward_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'} (hgg' : IntertwinesAlong (algebraMap F F') g g') (D : Divisor K F') : Divisor.pushforward F (g' • D) = g • Divisor.pushforward F D := by
  induction D using Finsupp.induction with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | single_add w n D _ _ ih =>
    rw [smul_add, map_add, map_add, smul_add, ih]
    congr 1
    rw [smul_single, Divisor.pushforward_single, Divisor.pushforward_single, smul_single,
      restrict_smul hgg' w, inertiaDeg_smul hgg' w]

end
