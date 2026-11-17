/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_regularDiffs_eq_regularDifferentials (git blob c9af9d7124a537d98ff6d9cae6fae003083dd4d3, sha256 3ae776298d9d1bf4410a2c3b19a7b9deb6c42a41b491d0d21886de70e4087de1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_regularDiffs_eq_regularDifferentials

set_option autoImplicit false

open AlgebraicCurve

namespace S12R

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_iff_ord_nonneg (w : Place K F) {x : F} (hx : x ≠ 0) :
    x ∈ w.toValuationSubring ↔ 0 ≤ w.ord x := by
  rw [Place.mem_iff_adicValuation_le_one, Place.ord, neg_nonneg,
    WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hx), WithZero.exp_zero]

theorem mem_of_ord_nonneg (w : Place K F) {x : F} (h : 0 ≤ w.ord x) : x ∈ w.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_mem _
  · exact (mem_iff_ord_nonneg w hx).mpr h

theorem ord_nonneg_of_mem (w : Place K F) {x : F} (h : x ∈ w.toValuationSubring) : 0 ≤ w.ord x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [Place.ord_zero]
  · exact (mem_iff_ord_nonneg w hx).mp h

theorem regularDiffs_eq [CharZero K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    regularDiffs K F = regularDifferentials K F := by
  haveI : PerfectField K := inferInstance
  haveI hgen : ∀ v : Place K F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver

  have key : ∀ (ω : Ω[F⁄K]) (v : Place K F),
      0 ≤ v.ordDiff ω ↔ ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord := by
    intro ω v
    rw [AlgebraicCurve.Place.ordDiff_eq_ordDifferential v ω]
    constructor
    · intro h
      exact ⟨v.differentialCoeff ω, mem_of_ord_nonneg v h, (v.differentialCoeff_smul_dCoord ω).symm⟩
    · rintro ⟨f, hf, rfl⟩
      show 0 ≤ v.ord (v.differentialCoeff (f • v.dCoord))
      rw [v.differentialCoeff_unique (rfl : f • v.dCoord = f • v.dCoord)]
      exact ord_nonneg_of_mem v hf
  apply le_antisymm
  · rw [regularDiffs_eq_span]
    refine Submodule.span_le.mpr (fun ω hω => ?_)
    rw [SetLike.mem_coe, mem_regularDifferentials_iff]
    exact fun v => (key ω v).mp (hω v)
  · intro ω hω
    rw [mem_regularDifferentials_iff] at hω
    exact mem_regularDiffs_of_isRegularDiff (fun v => (key ω v).mpr (hω v))

end S12R

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.regularDiffs K F = AlgebraicCurve.regularDifferentials K F := by
  exact S12R.regularDiffs_eq
