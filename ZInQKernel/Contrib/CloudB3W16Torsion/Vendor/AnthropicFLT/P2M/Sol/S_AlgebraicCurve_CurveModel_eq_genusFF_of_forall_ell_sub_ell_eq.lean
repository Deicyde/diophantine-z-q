/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_genusFF_of_forall_ell_sub_ell_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) {Kc : Divisor K L} {g : ℕ}
    (hRR : ∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    g = genusFF K L := by
  haveI : IsCurveOver K L :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one M.toBase M.ffEquiv
      M.ffEquiv_algebraMap
  haveI : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
  haveI : LocallyOfFiniteType M.toBase := inferInstance
  haveI : Algebra.EssFiniteType K L := by
    letI := M.functionFieldAlgebra
    haveI : Algebra.EssFiniteType K M.C.functionField := essFiniteType_functionField M.toBase
    exact Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.symm.toAlgHom M.ffAlgEquiv.symm.surjective

  haveI : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := M.C)) isClosed_univ.isLocallyClosed
  have hC : ConstantsAreBase K L :=
    constantsAreBase_of_deg_eq_one (M.placeOfPoint ⟨x, hx⟩)
      (IsCurveOver.deg_eq_one_of_isAlgClosed _)
  exact eq_genusFF_of_forall_ell_sub_ell_eq hC hRR
