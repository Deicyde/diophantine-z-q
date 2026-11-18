import ActualDivisionFieldV004
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The actual continuous finite quotient of the original Galois group

The quotient by the original torsion-action kernel is identified with the
actual division-field Galois group. Its topology is the genuine quotient
of the Krull topology, and is discrete because the kernel is open.
-/

noncomputable section
set_option autoImplicit false

namespace ActualDivisionField
open ActualFiniteLevel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [IsAlgClosure K Ω]
variable (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)]

def quotientEquiv : ((Ω ≃ₐ[K] Ω) ⧸ (action A m).ker) ≃*
    (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) :=
  QuotientGroup.liftEquiv (action A m).ker (restriction_surjective A m) (restriction_ker A m).symm

lemma quotientEquiv_apply (σ : Ω ≃ₐ[K] Ω) :
    quotientEquiv A m (QuotientGroup.mk σ) = restriction A m σ := rfl

instance quotient_discreteTopology : DiscreteTopology ((Ω ≃ₐ[K] Ω) ⧸ (action A m).ker) :=
  QuotientGroup.discreteTopology (kernel_isOpen A m)

instance quotient_finite : Finite ((Ω ≃ₐ[K] Ω) ⧸ (action A m).ker) :=
  Finite.of_equiv (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) (quotientEquiv A m).symm.toEquiv

def continuousQuotientEquiv : ((Ω ≃ₐ[K] Ω) ⧸ (action A m).ker) ≃ₜ*
    (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m) where
  toMulEquiv := quotientEquiv A m
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

lemma continuousQuotientEquiv_apply (σ : Ω ≃ₐ[K] Ω) :
    (continuousQuotientEquiv (Ω := Ω) A m).toMulEquiv (QuotientGroup.mk σ) = restriction A m σ := rfl

end ActualDivisionField
