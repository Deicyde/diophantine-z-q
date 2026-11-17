/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry open AlgebraicCurve hiding eq_genusFF_of_forall_ell_sub_ell_eq
theorem AlgebraicCurve.CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) {Kc : Divisor K L} {g : ℕ}
    (hRR : ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    g = genusFF K L := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq.solution
