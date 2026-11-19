/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag (git blob af13fc77a4f338f74a463b67adff8de9dcd10ad2, sha256 da3a3f134ddb8e78a745aede1022aab96aa06045f0b86c9bd81ca96d3d8369f9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Matrix.specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag
    (k : Matrix (Fin 2) (Fin 2) ℂ) (hk : k ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ a b c : ℝ,
      k = !![Complex.exp (a * Complex.I), 0; 0, Complex.exp (-(a * Complex.I))] *
            !![(Real.cos b : ℂ), -(Real.sin b : ℂ); (Real.sin b : ℂ), (Real.cos b : ℂ)] *
            !![Complex.exp (c * Complex.I), 0; 0, Complex.exp (-(c * Complex.I))] := by
  revert k hk
  exact @_root_.P2MW.S_Matrix_specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag.solution
