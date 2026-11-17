/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt (git blob f6d1fb80552a20e0d24ed27d0196676ea87e52d9, sha256 2c80ba392cc88afc5410a0c0a43ae2a6f6e9b4610e3b926d0382c49988968e99).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMapBundled
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt

set_option autoImplicit false

open UpperHalfPlane ModularCurve.Period

open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (Period.IsEquivariantPrimitive)
namespace PeriodHomWellDefined
open _root_.ModularCurve

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z) (fun σ => by have h__af := (hF σ).sub (hG σ); simp at h__af; exact h__af) τ UpperHalfPlane.I

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

theorem period_congr {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (c : ℂ) (h : ∀ z, F z - F' z = c) (γ : Γ) :
    hF.period γ = hF'.period γ := by
  rw [← hF.sub_eq_period γ UpperHalfPlane.I, ← hF'.sub_eq_period γ UpperHalfPlane.I]
  have h1 := h ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := h UpperHalfPlane.I
  linear_combination h1 - h2

end ModularCurve.PeriodHomWellDefined

open ModularCurve.PeriodHomWellDefined in
theorem solution {Γ : Subgroup SL(2, ℤ)}
    {F G : UpperHalfPlane → ℂ} {f : UpperHalfPlane → ℂ}
    (hF : ModularCurve.Period.IsEquivariantPrimitive Γ F)
    (hG : ModularCurve.Period.IsEquivariantPrimitive Γ G)
    (hFf : ∀ τ : UpperHalfPlane, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ)
    (hGf : ∀ τ : UpperHalfPlane, HasDerivAt (G ∘ UpperHalfPlane.ofComplex) (f τ) ↑τ) :
    hF.periodHom = hG.periodHom := by
  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hFf hGf
  refine DFunLike.ext _ _ fun γ => ?_
  show hF.period (Additive.toMul γ) = hG.period (Additive.toMul γ)
  exact period_congr hF hG c (fun z => by simpa [ofComplex_apply] using hc z) _

#print axioms solution
