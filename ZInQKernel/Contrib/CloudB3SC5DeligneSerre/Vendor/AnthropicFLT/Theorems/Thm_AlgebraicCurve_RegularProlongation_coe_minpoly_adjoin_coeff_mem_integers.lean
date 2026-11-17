/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers (git blob 884d4c59beea9fd4350c7d13b0a462572f74193b, sha256 92f9c7e382166316052edc02c60302883a4774e243f0d4d1decf7badbb1a5be3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) f)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V)
    (j : ℕ) :
    (((minpoly (Algebra.adjoin L ({(x : F)} : Set F)) f).coeff j :
      Algebra.adjoin L ({(x : F)} : Set F)) : F) ∈ R.integers := by
  revert L A F Fbar R x hx f hint h₃ j
  exact @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_coe_minpoly_adjoin_coeff_mem_integers.solution
