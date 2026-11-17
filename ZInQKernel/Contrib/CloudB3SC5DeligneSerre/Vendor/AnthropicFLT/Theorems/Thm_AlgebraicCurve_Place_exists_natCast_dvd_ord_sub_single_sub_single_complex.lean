/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex (git blob 9bb066d2b0d22575354aca9b857286bedf6a5610, sha256 498d7d58afc490262890a2ba4fdb57353a94d3e09259a69e8972d65f1937f9e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (n : ℕ) (hn : n ≠ 0) (P Q : Place ℂ F) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place ℂ F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor ℂ F) v := by
  revert F hfg n hn P Q
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex.solution
