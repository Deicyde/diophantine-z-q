/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_fundamentalIdentityAlong (git blob 1b5bf79601d9684d83af71531e04bf16f33d9f80, sha256 b57e61e5698eb10fa04ede4f35f93077b3c007b07812ceeb7d0c41d07c36e834).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_fundamentalIdentityAlong

open AlgebraicCurve AlgebraicCurve.SemilinearAut
open scoped Pointwise

noncomputable section

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) [HasPrincipalDivisors K F'] (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) : FundamentalIdentityAlong K φ hφ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : SumRamificationInertia K F F' := ⟨Place.sum_ramificationIndex_mul_inertiaDeg⟩
  exact (inferInstance : FundamentalIdentity K F F')

end
