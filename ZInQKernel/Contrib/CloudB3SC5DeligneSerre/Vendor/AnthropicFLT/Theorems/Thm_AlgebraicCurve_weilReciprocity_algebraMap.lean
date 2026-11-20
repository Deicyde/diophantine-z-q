/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_weilReciprocity_algebraMap (git blob a359dc705fdd6b7bc050aa96ec46b661537ec56f, sha256 4ba7fa76f0048f49951a44092f484db64c9a83a6fdb56b2f0a2a3a8857f135ab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_weilReciprocity_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.weilReciprocity_algebraMap {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F] [HasPrincipalDivisors K F'] (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠ 0) (Df Dg : Divisor K F') (hDf : ∀ w : Place K F', Df w = w.ord f) (hDg : ∀ w : Place K F', Dg w = w.ord (algebraMap F F' g)) (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) = 0) (hratf : ∀ w ∈ Df.support, Place.IsRational w) (hratF : ∀ v : Place K F, v.IsRational) (hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', Place.IsRational w) : Divisor.evalFun f Dg = Divisor.evalFun (algebraMap F F' g) Df := by
  revert K F F' hbase f g hf hg Df Dg hDf hDg hdisj hratf hratF hratfib
  exact @_root_.P2MW.S_AlgebraicCurve_weilReciprocity_algebraMap.solution
