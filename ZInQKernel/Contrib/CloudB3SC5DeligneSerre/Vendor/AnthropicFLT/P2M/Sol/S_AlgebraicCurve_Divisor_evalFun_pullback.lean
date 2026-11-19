/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_evalFun_pullback (git blob 9c6e4828d86354835f2115a247d70edee2059208, sha256 f2776468beeed871349b0886dbb67f27569af275d6eb3f90cb4385ab02c0f877).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_pairwiseDisjoint_fiber
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_support_pullback_subset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_evalFun_pullback

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (E : Divisor K F) (hrat : ∀ v ∈ E.support, Place.IsRational v) (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) : Divisor.evalFun f (Divisor.pullback F' E) = Divisor.evalFun (Algebra.norm F f) E := by
  classical
  rw [show evalFun f (pullback F' E)
      = ∏ w ∈ E.support.biUnion (fun v => v.fiber F'), w.evalAt f ^ (pullback F' E) w from
    Finsupp.prod_of_support_subset _ (AlgebraicCurve.Divisor.support_pullback_subset E)
      (fun w n => w.evalAt f ^ n) fun w _ => zpow_zero _,
    Finset.prod_biUnion (AlgebraicCurve.Place.pairwiseDisjoint_fiber E.support), evalFun_def]
  refine Finset.prod_congr rfl fun v hv => ?_
  calc
    ∏ w ∈ v.fiber F', w.evalAt f ^ (pullback F' E) w
        = ∏ w ∈ v.fiber F', (w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v := by
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [pullback_apply, Place.mem_fiber.mp hw, ← zpow_mul]
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F : ℤ)) ^ E v :=
          Finset.prod_zpow _ _ _
    _ = (∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F)) ^ E v := by
          refine congrArg (· ^ E v) (Finset.prod_congr rfl fun w _ => ?_)
          rw [zpow_natCast]
    _ = v.evalAt (Algebra.norm F f) ^ E v := by
          rw [AlgebraicCurve.Place.evalAt_norm_eq_prod_fiber v f hf (hrat v hv) (hratw v hv) (hord v hv)]
