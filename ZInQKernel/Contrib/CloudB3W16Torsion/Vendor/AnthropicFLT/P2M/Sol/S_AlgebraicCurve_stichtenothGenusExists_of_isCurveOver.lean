/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver

open IntermediateField
open AlgebraicCurve
-- Deferred synthetic P2M scope: root namespace remains open.

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver ConstantsAreBase StichtenothGenusExists IsCurveOver.exists_separating_transcendental RationalFunctionField.stichtenothGenusExists)
namespace TowerFreePort
open AlgebraicCurve
theorem solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F := by
  classical
  obtain ⟨x, htr, hfd, hsep⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := hfd; haveI := hsep
  set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x htr with he
  letI : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact RationalFunctionField.stichtenothGenusExists K F hC

end AlgebraicCurve.TowerFreePort

open IntermediateField _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.AlgebraicCurve in
theorem solution {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] (hC : ConstantsAreBase K F) :
    StichtenothGenusExists K F :=
  AlgebraicCurve.TowerFreePort.solution hC
