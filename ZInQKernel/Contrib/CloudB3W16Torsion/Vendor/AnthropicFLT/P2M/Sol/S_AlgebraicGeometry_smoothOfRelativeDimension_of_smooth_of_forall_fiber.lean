/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x

  obtain ⟨m, hm⟩ : ∃ m : ℕ, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    letI := (f.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hstd
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

  obtain ⟨U', V', hV', hxV', e', hm'⟩ :=
    AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField f x m U hU V hV hxV e hm
  have hmn : m = n :=
    AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
      (f.fiberToSpecResidueField (f.base x)) n (h (f.base x)) m U' V' hV' (f.asFiber x) hxV' e' hm'
  subst hmn
  exact ⟨U, hU, V, hV, hxV, e, hm⟩
