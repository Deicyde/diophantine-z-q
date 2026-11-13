import ImportedRhoCont
import TateRank
import ZInQKernel.HDecomp.C10.C10

/-
DRAFT binding of the existing e303 RhoCont proof to the checked original Tate
supplier. No continuity reproof and no copied Objects/QM definitions.

ImportedRhoCont is the exact selected source file relocated as a standalone
optional-package module; its mathematics and PkgI3 names must be preserved and
its new import/module/options context must be compiled and checked before use.
This file is not yet compiled or independently reviewed.
-/

noncomputable section

namespace AxiomBridge.NativeContinuity

variable {K : Type} [Field K]

/-- Native Galois matrix-coefficient continuity in every genuine finite basis,
with the original integral-module hypotheses constructed, not assumed. -/
theorem continuous_toMatrix_galRep (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.toMatrix b b (A.galRep ℓ σ)) := by
  have hT := AxiomBridge.TateConsumer.tateModuleFree K A ℓ hℓ
  letI := hT.1
  letI := hT.2.1
  exact PkgI3.RhoCont.continuous_toMatrix_galRep ℓ A b

/-- Native trace continuity from the same original Tate input. -/
theorem continuous_trace_galRep (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) := by
  exact (PkgI3.continuous_galRep_of_tateModuleFree
    AxiomBridge.TateConsumer.tateModuleFree A ℓ hℓ).2

/-- The exact matrix-continuity input of C10 on the full native AV-side
representation at three. This does not identify it with the descended/scaled r₃. -/
theorem c10_three_native_matrix_continuous (A : PkgI3.AbVar ℚ)
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[3] (A.V 3)) :
    Continuous (fun g : GlueC10.GQ =>
      LinearMap.toMatrix b b (A.galRep 3 g)) := by
  exact continuous_toMatrix_galRep A 3 (by norm_num) b

/-- Continuous native AV trace on C10's actual GQ, for either selected prime
when its original invertibility condition is supplied. -/
theorem c10_native_trace_continuous (A : PkgI3.AbVar ℚ) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : (ℓ : ℚ) ≠ 0) :
    Continuous (fun g : GlueC10.GQ =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ g)) := by
  exact continuous_trace_galRep A ℓ hℓ

end AxiomBridge.NativeContinuity

#check AxiomBridge.NativeContinuity.continuous_toMatrix_galRep
#check AxiomBridge.NativeContinuity.c10_three_native_matrix_continuous
#print axioms AxiomBridge.NativeContinuity.continuous_toMatrix_galRep
#print axioms AxiomBridge.NativeContinuity.continuous_trace_galRep
#print axioms AxiomBridge.NativeContinuity.c10_three_native_matrix_continuous
#print axioms AxiomBridge.NativeContinuity.c10_native_trace_continuous
