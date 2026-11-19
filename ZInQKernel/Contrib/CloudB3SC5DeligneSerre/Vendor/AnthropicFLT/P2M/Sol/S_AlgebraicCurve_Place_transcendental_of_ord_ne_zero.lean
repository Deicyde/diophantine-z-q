/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero (git blob d3711f0f2d86a3f868682cc23b5d27e6fed719c0, sha256 c6e8829972f10475b8a8792b29bafb7581a9749f0d992bfbe486e04f6a8ea225).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Mathlib.RingTheory.Algebraic.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero

noncomputable section
open Polynomial

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place.mem_of_eval_monic_eq_zero Place)
namespace Place
export _root_.AlgebraicCurve.Place (mem_of_eval_monic_eq_zero ext ord ord_zero ord_coe_unit algebraMap_mem' toValuationSubring)
namespace FF2R0
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

private theorem mem_of_isAlgebraic {x : F} (hx : IsAlgebraic K x) : x ∈ v.toValuationSubring := by
  have hint : IsIntegral K x := hx.isIntegral
  refine v.mem_of_eval_monic_eq_zero (P := (minpoly K x).map (algebraMap K F)) ((minpoly.monic hint).map _)
    (fun i => ?_) ?_
  · rw [coeff_map]; exact v.algebraMap_mem' _
  · rw [eval_map_algebraMap, minpoly.aeval]

theorem ord_eq_zero_of_isAlgebraic' {x : F} (hx : IsAlgebraic K x) : v.ord x = 0 := by
  by_cases hx0 : x = 0
  · simp [hx0, v.ord_zero]
  · let u : v.toValuationSubringˣ :=
      { val := ⟨x, mem_of_isAlgebraic v hx⟩
        inv := ⟨x⁻¹, mem_of_isAlgebraic v hx.inv⟩
        val_inv := Subtype.ext (mul_inv_cancel₀ hx0)
        inv_val := Subtype.ext (inv_mul_cancel₀ hx0) }
    exact v.ord_coe_unit u

end AlgebraicCurve.Place.FF2R0

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t :=
  fun h => ht (AlgebraicCurve.Place.FF2R0.ord_eq_zero_of_isAlgebraic' v h)

end
