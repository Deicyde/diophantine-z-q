/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (git blob 7edd4f94c689576c60e17c55a86ef54d52aa8ac6, sha256 fa75671414e3ad98c8afbe6cb206533a2ce917846a544f5ff0419bd9e4497067).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_qExpand_image_intFormRatiosC_subset

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0

set_option autoImplicit false

theorem solution
    (K : Type*) [Field K] (M : ℕ) [NeZero M] :
    ModularCurve.modularFunctionFieldFullC K M ≤
      ModularCurve.qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) := by
  rw [ModularCurve.modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd, hdM, rfl⟩
  haveI := hd
  refine ModularCurve.intFormRatiosC_subset K _ ?_

  have hle : CongruenceSubgroup.Gamma0 M ≤ CongruenceSubgroup.Gamma0 d := by
    intro γ hγ
    rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
    exact (Int.natCast_dvd_natCast.mpr hdM).trans hγ
  refine ModularCurve.intFormRatiosC_mono K hle ?_

  refine ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := ⊤)
    (Γ' := CongruenceSubgroup.Gamma0 d) (Subgroup.mem_top _) d ?_
    ⟨_, ModularCurve.jqModC_mem_intFormRatiosC K ⊤, rfl⟩
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact Matrix.SpecialLinearGroup.det_coe γ
  rw [hc] at hdet
  refine ⟨⟨!![γ 0 0, (d : ℤ) * γ 0 1; c, γ 1 1], ?_⟩, Subgroup.mem_top _, rfl, rfl, ?_, rfl⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet
  · show (d : ℤ) * c = γ 1 0
    rw [hc]
