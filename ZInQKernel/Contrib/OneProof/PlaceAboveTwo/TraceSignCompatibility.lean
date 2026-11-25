import ZInQKernel.Contrib.OneProof.PlaceAboveTwo.TraceOne
import ZInQKernel.Contrib.OneProof.PlaceAboveTwo.SignLine

/-!
# Compatibility between the integral trace and the first sign-line reduction

This bridge imports the independent integral trace-one and sign-line modules.
The integral endpoint therefore has no import dependency on the sign-line port.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.PlaceAboveTwo

open CategoryTheory
open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.Duality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTrace

variable (F : Type) [Field F] [CharZero F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The first reduction of any integral cycle is the sign class of the same trace value. -/
theorem first_reduction_eq_sign_iff (z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom)
    (x : (SignLine.signComplex F).homology 2) :
    actualMuH2Reduction F 1 z = SignLine.kummerClass F x ↔
      PadicInt.toZModPow 1 (AllCochainTrace.trv F z.val) = SignLine.invariant F x := by
  rw [AllCochainTrace.trv_finite_normalization, ← SignLine.finiteInvariant_kummerClass]
  exact (FiniteTrace.finiteInvariant F 2 (isUnit_iff_ne_zero.mpr two_ne_zero)).injective.eq_iff.symm

/-- The integral cycle has trace one and its first class matches the normalized sign class. -/
theorem exists_trace_one_with_sign :
    ∃ z : LinearMap.ker ((actualTraceComplex F).d 2 3).hom,
      AllCochainTrace.trv F z.val = 1 ∧
      actualMuH2Reduction F 1 z = SignLine.kummerClass F ((SignLine.invariant F).symm 1) := by
  obtain ⟨z, h⟩ := exists_trace_one F
  refine ⟨z, h, (first_reduction_eq_sign_iff F z _).2 ?_⟩
  rw [h, map_one, LinearEquiv.apply_symm_apply]


end ZInQ.Contrib.RC53Assist.PlaceAboveTwo

end
