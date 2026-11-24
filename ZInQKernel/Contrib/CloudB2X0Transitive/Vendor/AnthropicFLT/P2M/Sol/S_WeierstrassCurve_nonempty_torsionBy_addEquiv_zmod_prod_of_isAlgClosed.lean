/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
[port] Tau Ceti name clash: renamed `Coeff` → `Coeff_aflt`, `ψc_neg` → `ψc_neg_aflt`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
attribute [-instance] WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly
attribute [-simp] compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff_aflt.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff_aflt.A₆.sizeOf_spec WeierstrassCurve.ψc_neg_aflt WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff_aflt.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff_aflt.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff_aflt.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem solution
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W⁄K).Point n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  refine AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq hn0 ?_
  intro d hd
  have hdK : (d : K) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hd
    intro h; apply hn; push_cast; rw [h, zero_mul]
  exact W.card_torsion_of_isAlgClosed hdK
