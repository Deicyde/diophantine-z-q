/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PeriodPair_g2_ofTau_and_g3_ofTau (git blob adbf89217a22b587a8ce0833e632236dd4f78e48, sha256 a307fa00b88712256d02acd74c6cc139f03249729d23ad5de694c0a2be4112bd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace PeriodPair
end PeriodPair
namespace P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau.PeriodPair
end P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau.PeriodPair

namespace P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm EisensteinSeries Complex
open scoped MatrixGroups Real Topology

namespace PeriodPair
export _root_.PeriodPair (latticeEquivProd g₃ latticeEquiv_symm_apply G g₂ ofTau ofTau_ω₁ ofTau_ω₂)
namespace EisensteinBridge
open _root_.PeriodPair
open _root_.PeriodPair
open _root_.P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau.PeriodPair

theorem G_ofTau_eq {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ofTau τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  rw [PeriodPair.G, ← (ofTau τ).latticeEquivProd.symm.toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, ofTau_ω₁, ofTau_ω₂, mul_one]
  have hstep : ∀ p : ℤ × ℤ,
      ((↑p.1 * (τ : ℂ) + ↑p.2) ^ k)⁻¹ = eisSummand k ((finTwoArrowEquiv ℤ).symm p) τ := by
    intro p
    simp only [eisSummand, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zpow_neg, zpow_natCast]
  simp only [hstep]
  rw [(finTwoArrowEquiv ℤ).symm.tsum_eq (f := fun v => eisSummand (k : ℤ) v τ),
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ,
    show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    eisensteinSeriesSIF_apply, smul_eq_mul]
  ring

theorem g₂_ofTau (τ : ℍ) : (ofTau τ).g₂ = (120 * riemannZeta 4) * E₄ τ := by
  rw [PeriodPair.g₂, G_ofTau_eq (by norm_num : 3 ≤ 4)]; push_cast; ring

theorem g₃_ofTau (τ : ℍ) : (ofTau τ).g₃ = (280 * riemannZeta 6) * E₆ τ := by
  rw [PeriodPair.g₃, G_ofTau_eq (by norm_num : 3 ≤ 6)]; push_cast; ring

end PeriodPair.EisensteinBridge

open PeriodPair.EisensteinBridge in
theorem solution (τ : UpperHalfPlane) :
    (PeriodPair.ofTau τ).g₂ = 120 * riemannZeta 4 * ModularForm.E₄ τ ∧
      (PeriodPair.ofTau τ).g₃ = 280 * riemannZeta 6 * ModularForm.E₆ τ :=
  ⟨g₂_ofTau τ, g₃_ofTau τ⟩
