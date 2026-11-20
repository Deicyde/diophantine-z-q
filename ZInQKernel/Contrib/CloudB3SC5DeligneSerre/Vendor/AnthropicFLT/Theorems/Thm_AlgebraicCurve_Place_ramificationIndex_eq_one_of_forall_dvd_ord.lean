/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord (git blob 55697d490efbad10b7f64a3a59683cce5bdb8e02, sha256 cb742fcc8a3b9d5f360929affe24c0aacb16fae0d26b1915943457d2ce2cee87).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve IntermediateField
theorem AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord {K F L : Type*} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {p : ℕ} [Fact p.Prime] {f : F} {α : L} [CharZero F]
    (hf : ∀ g : F, g ^ p ≠ f)
    (hα : α ^ p = algebraMap F L f) (htop : F⟮α⟯ = ⊤)
    (hord : ∀ v : Place K F, (p : ℤ) ∣ v.ord f)
    (w : Place K L) (hw_rat : w.IsRational) :
    w.ramificationIndex F = 1 := by
  revert K F L p f α hf hα htop hord w hw_rat
  exact @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord.solution
