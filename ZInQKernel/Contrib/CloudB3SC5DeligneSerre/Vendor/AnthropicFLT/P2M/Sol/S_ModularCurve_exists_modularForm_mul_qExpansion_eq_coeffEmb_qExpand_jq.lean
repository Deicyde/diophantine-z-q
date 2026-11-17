/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq (git blob 7a206d8c19b449592f6d3a484817e986fd6b3f59, sha256 ca16b8521561b23f2c0e3a76679a808189864debaa3e42cdcf3b024c52472c02).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve
end P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve
namespace P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel
end P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel

namespace P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve
export _root_.ModularCurve (qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jq coeffEmb coeffEmb_coeff jqModC jqNModC jqModC_rat map_jqModC exists_gamma0_qExpansion_div_eq_jqNModC)
namespace JqdRatioOfLevel
open _root_.ModularCurve

theorem coeffEmb_qExpand_eq (d : ℕ) [NeZero d] (x : LaurentSeries ℚ) :
    coeffEmb ℂ (qExpand ℚ d x) = qExpand ℂ d (coeffEmb ℂ x) := by
  ext k
  by_cases hk : (d : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd (hk := hk), qExpand_coeff_of_not_dvd (hk := hk),
      map_zero]

theorem coeffEmb_jq_eq : coeffEmb ℂ jq = jqModC ℂ := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ ℂ)

theorem coeffEmb_qExpand_jq_eq (d : ℕ) [NeZero d] :
    coeffEmb ℂ (qExpand ℚ d jq) = jqNModC ℂ d := by
  rw [coeffEmb_qExpand_eq, coeffEmb_jq_eq]
  rfl

theorem Gamma0_le_of_dvd {d N : ℕ} (hd : d ∣ N) :
    CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 d := by
  intro A hA
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact (Int.natCast_dvd_natCast.mpr hd).trans hA

theorem Gamma0GL_le_of_dvd {d N : ℕ} (hd : d ∣ N) :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 d : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (Gamma0_le_of_dvd hd)

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn f γ (hle hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono hle)

@[scoped simp]
theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) : ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

theorem restrict_ne_zero {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    {f : ModularForm Γ k} (hf : f ≠ 0) : restrict hle f ≠ 0 := by
  intro h
  apply hf
  apply DFunLike.ext
  intro z
  have := congrArg (fun g : ModularForm Γ' k => (g : ℍ → ℂ) z) h
  simpa using this

theorem one_mem_strictPeriods (d : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 d : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem qExpansion_coe_ne_zero {d : ℕ} {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 d) k)
    (hf : f ≠ 0) : ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
  intro h
  apply hf
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods d)]
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  simpa using h

end ModularCurve.JqdRatioOfLevel
open scoped _root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve _root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel
open scoped _root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve _root_.P2MW.S_ModularCurve_exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq.ModularCurve.JqdRatioOfLevel

open UpperHalfPlane in
open ModularCurve.JqdRatioOfLevel in
theorem solution (N d : ℕ)
    [NeZero N] [NeZero d] (hd : d ∣ N) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k), h ≠ 0 ∧
      ModularCurve.coeffEmb ℂ (ModularCurve.qExpand ℚ d ModularCurve.jq) *
          ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  obtain ⟨G, H, hH, hdiv⟩ := ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC d
  have hle := Gamma0GL_le_of_dvd hd
  refine ⟨12, restrict hle G, restrict hle H, restrict_ne_zero hle hH, ?_⟩
  rw [coe_restrict, coe_restrict, ModularCurve.JqdRatioOfLevel.coeffEmb_qExpand_jq_eq, ← hdiv]
  exact div_mul_cancel₀ _ (qExpansion_coe_ne_zero H hH)
