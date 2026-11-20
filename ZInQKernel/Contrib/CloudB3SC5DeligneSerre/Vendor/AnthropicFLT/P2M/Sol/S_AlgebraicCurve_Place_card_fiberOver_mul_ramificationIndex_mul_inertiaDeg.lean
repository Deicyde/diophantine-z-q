/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (git blob 431941c4a40e3d950d4b85ebc3fa2e6e366183fe, sha256 aa228d961d13450da39dbc96eb8bac9b5973de8ff26d3f7145faf9f838de393f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.FieldTheory.Galois.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_of_restrict_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_of_restrict_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.AlgebraicCurve
namespace IsDedekindDomain
end IsDedekindDomain
namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg

set_option autoImplicit false
noncomputable section
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.AlgebraicCurve
open _root_.IsDedekindDomain
open scoped Pointwise

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ramificationIndex_eq_of_restrict_eq Place.inertiaDeg_eq_of_restrict_eq)
open _root_.AlgebraicCurve
namespace Place
export _root_.AlgebraicCurve.Place (fiberOver restrict_eq_of_mem_fiberOver ramificationIndex restrict inertiaDeg ramificationIndex_eq_of_restrict_eq inertiaDeg_eq_of_restrict_eq sum_ramificationIndex_mul_inertiaDeg_fiberOver)
open _root_.AlgebraicCurve.Place

variable {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
  [Algebra F' M] [IsScalarTower K F' M]

end Place
end AlgebraicCurve

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_card_fiberOver_mul_ramificationIndex_mul_inertiaDeg.AlgebraicCurve.Place in
theorem solution {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [IsGalois F' M] (w : Place K F') (W : Place K M)
    (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') = Module.finrank F' M := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  have hconst : ∀ W' ∈ w.fiberOver M,
      (W'.ramificationIndex F' : ℤ) * (W'.inertiaDeg F' : ℤ)
        = (W.ramificationIndex F' : ℤ) * (W.inertiaDeg F' : ℤ) := by
    intro W' hW'
    have h : W'.restrict F' = W.restrict F' :=
      (restrict_eq_of_mem_fiberOver w hW').trans hW.symm
    rw [Place.ramificationIndex_eq_of_restrict_eq W W' h, Place.inertiaDeg_eq_of_restrict_eq W W' h]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  exact_mod_cast hsum

end
