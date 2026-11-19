/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_mul (git blob 70aff7ffa9257a49918d0e8e9854923d0e525254, sha256 9cde676c19cb551b6e1e0c308b63d7ba02ef7dbe5dfbf268fc9a539ae46b34ca).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_mul

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {f g : F} {D : Divisor K F} (hrat : ∀ v ∈ D.support, Place.IsRational v) (hf : ∀ v ∈ D.support, f ∈ v.toValuationSubring) (hg : ∀ v ∈ D.support, g ∈ v.toValuationSubring) : Divisor.evalFun (f * g) D = Divisor.evalFun f D * Divisor.evalFun g D := by
  rw [show Divisor.evalFun (f * g) D = D.prod fun v n => v.evalAt f ^ n * v.evalAt g ^ n from
    Finsupp.prod_congr fun v hv => by
      rw [AlgebraicCurve.Place.evalAt_mul v (hrat v hv) (hf v hv) (hg v hv), mul_zpow]]
  exact Finsupp.prod_mul
