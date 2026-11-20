/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card

set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (hcard : r + 1 ≤ S.card)
    (D : Divisor K F) (hdeg : Divisor.degree D = r) :
    ∃ f : Fin (r - g) → Place K F, Function.Injective f ∧ (∀ j, f j ∈ S) ∧
      ell (D - ∑ j : Fin (r - g), Finsupp.single (f j) 1) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card.solution
