/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (git blob a7fcb05993f2d3751f2cb1cff15cffa4c8b3bf6e, sha256 ac2430bee67ce6f0873f5acaaed6447508ad6b8b270565694f8514eb44a4cf71).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq

set_option autoImplicit false

noncomputable section

open PeriodPair

theorem solution (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (h : L.weierstrassP a = L.weierstrassP b) :
    a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by
  have hΔ : L.DiscriminantNeZero := PeriodPair.discriminant_ne_zero L
  obtain ⟨hadd, -, hker⟩ := PeriodPair.isUniformization_toPoint L hΔ

  have hsq : L.derivWeierstrassP a ^ 2 = L.derivWeierstrassP b ^ 2 := by
    rw [L.derivWeierstrassP_sq a ha, L.derivWeierstrassP_sq b hb, h]

  have hneg : ∀ z : ℂ, L.toPoint hΔ (-z) = -L.toPoint hΔ z := by
    intro z
    have h0 := hadd z (-z)
    rw [add_neg_cancel, toPoint_zero] at h0
    exact (neg_eq_of_add_eq_zero_right h0.symm).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hd | hd
  ·
    left
    apply hker
    have hab : L.toPoint hΔ a = L.toPoint hΔ b := by
      rw [toPoint_of_notMem L hΔ ha, toPoint_of_notMem L hΔ hb]
      congr 1 <;> simp [hd]
    rw [sub_eq_add_neg, hadd, hneg, hab, add_neg_cancel]
  ·
    right
    apply hker
    have hab : L.toPoint hΔ a = -L.toPoint hΔ b := by
      rw [toPoint_of_notMem L hΔ ha, toPoint_of_notMem L hΔ hb,
        WeierstrassCurve.Affine.Point.neg_some]
      congr 1 <;> simp [WeierstrassCurve.Affine.negY, h, hd, neg_div]
    rw [hadd, hab, neg_add_cancel]
