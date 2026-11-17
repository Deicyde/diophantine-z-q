/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber (git blob dd5bb1d5db225a743a1931e93d0f0b91acf29d14, sha256 a04f4cd403a2582101fb6b66458c9aac8a59e4d7e6954705773c29587e587f17).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_pairwiseDisjoint_fiber

open AlgebraicCurve

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] (s : Finset (Place K F)) : Set.PairwiseDisjoint (s : Set (Place K F)) (fun v : Place K F => v.fiber F') := by
  intro v₁ _ v₂ _ hne
  refine Finset.disjoint_left.mpr fun w hw₁ hw₂ => ?_
  exact hne ((Place.mem_fiber.mp hw₁).symm.trans (Place.mem_fiber.mp hw₂))
