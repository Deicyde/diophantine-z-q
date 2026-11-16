/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution {X : Scheme.{u}} {I : X.IdealSheafData} (hI : I.IsInvertible) (n : ℕ) :
    (I ^ n).IsInvertible := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hI
