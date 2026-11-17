/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul (git blob 33904d7f65e5bc034ea52ad0cd78874270f9fce0, sha256 45912fdd0daac31a88dd3cbe83a51beb14abd7f91d0c46eb85194ee9a3e6e895).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve
namespace IsDedekindDomain
end IsDedekindDomain
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul

set_option autoImplicit false
noncomputable section
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ext SemilinearAut SemilinearAut.inv_smul_def SemilinearAut.ofAlgAut SemilinearAut.toRingAut_ofAlgAut SemilinearAut.smul_toValuationSubring)
open _root_.AlgebraicCurve
namespace Place
export _root_.AlgebraicCurve.Place (restrict restrict_toValuationSubring ext smul_toValuationSubring)
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_restrict_ofAlgAut_smul.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [Algebra.IsIntegral F' M] (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F' := by
  refine Place.ext ?_
  ext x
  rw [restrict_toValuationSubring, restrict_toValuationSubring, ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, SemilinearAut.inv_smul_def,
    SemilinearAut.toRingAut_ofAlgAut]
  change ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) ∈ _ ↔ _
  have : ((σ.restrictScalars K : M ≃+* M).symm (algebraMap F' M x)) = algebraMap F' M x := by
    rw [RingEquiv.symm_apply_eq]
    exact (σ.commutes x).symm
  rw [this]

end
