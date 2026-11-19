/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single (git blob 2a5315faa67c31041d613efa650470c7fe9a55d9, sha256 7038eddbee01b46f297cd888e6d27a94a8136830733e163d4d9f0a4f4f0db5c9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single (K F : Type*) [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (n : ℕ) (hn : n ≠ 0) (P Q : Place K F) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) v := by
  revert K F hfg n hn P Q
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single.solution
