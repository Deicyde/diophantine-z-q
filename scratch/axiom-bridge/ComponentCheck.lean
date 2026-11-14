import TateRank
import NativeContinuity
import C10Frobenius
import C10PrimeField
import C10FiniteField
import C10FieldPoints

/-!
Lightweight CI statement/axiom checks for the opt-in consumers. The dedicated
trust-zero body/environment/control checks and their failure history are recorded
separately; this file does not claim a full external-library replay.
-/

example : PkgI3.TateModuleFree := AxiomBridge.TateConsumer.tateModuleFree

example {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)) :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.toMatrix b b (A.galRep ℓ σ)) :=
  AxiomBridge.NativeContinuity.continuous_toMatrix_galRep A ℓ hℓ b

example {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) :
    Continuous (fun σ : Field.absoluteGaloisGroup K =>
      LinearMap.trace ℚ_[ℓ] (A.V ℓ) (A.galRep ℓ σ)) :=
  AxiomBridge.NativeContinuity.continuous_trace_galRep A ℓ hℓ

#print axioms AxiomBridge.pointsBaseChangeMulEquiv
#print axioms AxiomBridge.pointsBaseChangeMulEquiv_natural
#print axioms AxiomBridge.TateConsumer.tate_free_finite
#print axioms AxiomBridge.TateConsumer.rational_tate_finite
#print axioms AxiomBridge.TateConsumer.tateModuleFree
#print axioms AxiomBridge.NativeContinuity.continuous_toMatrix_galRep
#print axioms AxiomBridge.NativeContinuity.continuous_trace_galRep
#print axioms AxiomBridge.NativeContinuity.c10_three_native_matrix_continuous
#print axioms AxiomBridge.NativeContinuity.c10_native_trace_continuous
