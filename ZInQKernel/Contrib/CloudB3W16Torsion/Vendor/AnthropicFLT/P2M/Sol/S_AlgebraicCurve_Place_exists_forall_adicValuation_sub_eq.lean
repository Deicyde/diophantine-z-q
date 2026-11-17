/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_neg
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_eq

set_option autoImplicit false

open AlgebraicCurve in

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) = WithZero.exp (n v) := by
  obtain ⟨f₀, hf₀⟩ := Place.exists_forall_adicValuation_sub_le T β (fun v => n v - 1)
  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq_finset T (fun v => -n v)
  refine ⟨f₀ + g, fun v hv => ?_⟩
  have hgv : v.ord g = -n v := hg v hv
  have hval_g : v.adicValuation g = WithZero.exp (n v) := by
    rw [v.adicValuation_eq_exp_neg_ord hg0, hgv, neg_neg]
  have hsplit : f₀ + g - β v = g + (f₀ - β v) := by ring
  rw [hsplit]
  rcases eq_or_ne (f₀ - β v) 0 with h0 | h0
  · rw [h0, add_zero, hval_g]
  · have hord : 1 - n v ≤ v.ord (f₀ - β v) := by
      have := (v.adicValuation_le_exp_iff).mp (hf₀ v hv)
      rcases this with h | h
      · exact absurd h h0
      · omega
    have hlt : v.ord g < v.ord (f₀ - β v) := by rw [hgv]; omega
    have hne : g + (f₀ - β v) ≠ 0 := by
      intro hz
      rw [eq_neg_of_add_eq_zero_right hz, v.ord_neg] at hlt
      exact lt_irrefl _ hlt
    rw [v.adicValuation_eq_exp_neg_ord hne, v.ord_add_eq_of_lt hg0 h0 hlt, hgv, neg_neg]
