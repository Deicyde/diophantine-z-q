/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq (git blob fef4003874dd5ba19956934f176c51d0e0f05257, sha256 daae7eacdcdd3d85d0e12ed1af519dc2f14d678c19a7364bb510436aaf874c44).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Galois.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_ramificationIndex_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.AlgebraicCurve
namespace IsDedekindDomain
end IsDedekindDomain
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq

set_option autoImplicit false
noncomputable section
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
export _root_.AlgebraicCurve (SemilinearAut.IntertwinesAlong Place SemilinearAut SemilinearAut.ofAlgAut SemilinearAut.ofAlgAut_smul Place.exists_algEquiv_smul_eq_of_restrict_eq SemilinearAut.ramificationIndex_smul)
open _root_.AlgebraicCurve
namespace Place
export _root_.AlgebraicCurve.Place (ramificationIndex restrict exists_algEquiv_smul_eq_of_restrict_eq)
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

private theorem intertwinesAlong_one_ofAlgAut (σ : M ≃ₐ[F'] M) :
    SemilinearAut.IntertwinesAlong (algebraMap F' M) (1 : SemilinearAut K F')
      (SemilinearAut.ofAlgAut (σ.restrictScalars K)) := by
  intro x
  rw [one_smul, SemilinearAut.ofAlgAut_smul]
  exact σ.commutes x

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (W W' : Place K M)
    (h : W'.restrict F' = W.restrict F') :
    W'.ramificationIndex F' = W.ramificationIndex F' := by
  obtain ⟨σ, rfl⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h
  exact SemilinearAut.ramificationIndex_smul (intertwinesAlong_one_ofAlgAut σ) W

end
