/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward (git blob 9e3ee9fdd2ded4b1bf9626d8abcdf432c40302b1, sha256 49d5365b02f6ac9c994598db9229c49c5c2b3c124690d382550df76c43eaa3a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] {g : F} (hg : g ≠ 0) (D : Divisor K F') (hratw : ∀ w ∈ D.support, Place.IsRational w) (hratv : ∀ w ∈ D.support, (w.restrict F).IsRational) (hord : ∀ w ∈ D.support, (w.restrict F).ord g = 0) : Divisor.evalFun (algebraMap F F' g) D = Divisor.evalFun g (Divisor.pushforward F D) := by
  revert K F F' g hg D hratw hratv hord
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward.solution
