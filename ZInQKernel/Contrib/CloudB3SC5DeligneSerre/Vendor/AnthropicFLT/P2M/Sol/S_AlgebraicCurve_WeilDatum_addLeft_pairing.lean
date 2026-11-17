/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_WeilDatum_addLeft_pairing (git blob 014de4bf53d09a963412677417ddbf4fcf0d75c0, sha256 4fedd0e14d7d5d10de9d1f7181de8b6f318e1d4ed4bb4f07cf0e167b3e074f24).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_WeilDatum
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_ne_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_mul
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_evalFun_add
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_of_ord_nonneg
import Batteries.Tactic.Alias

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve
end P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve
namespace AlgebraicCurve.WeilDatum
end AlgebraicCurve.WeilDatum

namespace P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (WeilDatum WeilDatum.pairing Divisor.evalFun Place Divisor Place.evalAt_ne_zero Divisor.evalFun_ne_zero Divisor.evalFun_mul Divisor.evalFun_add)
namespace WeilDatum
export _root_.AlgebraicCurve.WeilDatum (pairing addLeft f₁ ord_f₁ D₁ f₁_ne_zero disjoint ord_f₂ D₂ f₂_ne_zero f₂ rational)
open _root_.AlgebraicCurve.WeilDatum
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n)

private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

alias ord_f₁_eq_zero_of_mem_support' := _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support'
private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

alias ord_f₂_eq_zero_of_mem_support' := _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support'
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

alias rational_of_mem_support_left' := _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left'
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

alias rational_of_mem_support_right' := _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right'
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₁_ne_zero' {v : Place K F} (hv : v ∈ d.D₂.support) :
    v.evalAt d.f₁ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_right' hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support' hv)

alias evalAt_f₁_ne_zero' := _root_.AlgebraicCurve.WeilDatum.evalAt_f₁_ne_zero'
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero' {v : Place K F} (hv : v ∈ d.D₁.support) :
    v.evalAt d.f₂ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_left' hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support' hv)

alias evalAt_f₂_ne_zero' := _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero'
private theorem evalFun_f₁_ne_zero' : Divisor.evalFun d.f₁ d.D₂ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₁_ne_zero' hv

private theorem evalFun_f₂_ne_zero' : Divisor.evalFun d.f₂ d.D₁ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₂_ne_zero' hv

end AlgebraicCurve.WeilDatum

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_WeilDatum_addLeft_pairing.AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) : (d.addLeft d' hD hf).pairing = d.pairing * d'.pairing := by
  have hnum : Divisor.evalFun (d.f₁ * d'.f₁) d.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun d'.f₁ d.D₂ := by
    refine AlgebraicCurve.Divisor.evalFun_mul (fun v hv => d.rational_of_mem_support_right' hv)
      (fun v hv => ?_) (fun v hv => ?_)
    · exact v.mem_of_ord_nonneg d.f₁_ne_zero (d.ord_f₁_eq_zero_of_mem_support' hv).ge
    · exact v.mem_of_ord_nonneg d'.f₁_ne_zero
        (d'.ord_f₁_eq_zero_of_mem_support' (hD ▸ hv)).ge
  have hden : Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ d'.D₁ := by
    refine AlgebraicCurve.Divisor.evalFun_add d.f₂ (fun v hv => d.evalAt_f₂_ne_zero' hv) (fun v hv => ?_)
    exact hf ▸ d'.evalAt_f₂_ne_zero' hv
  show Divisor.evalFun (d.f₁ * d'.f₁) d.D₂ / Divisor.evalFun d.f₂ (d.D₁ + d'.D₁)
      = d.pairing * d'.pairing
  simp only [WeilDatum.pairing]
  rw [hnum, hden, div_mul_div_comm, hD, hf]
