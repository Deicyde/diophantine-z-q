import ActualCanonicalDivisionActionV002
import ActualDivisionCompatibilityV002

/-!
# Original Tate evaluation factors through the actual division fields

These point and level compatibilities need no finite-point premise: the
closed original kernel already gives the actual normal division-field
action. Geometric finiteness is only needed to make the fields finite.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualClosedDivisionKernel
open ActualFiniteLevel ActualDivisionField ActualDivisionCompatibility
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [IsAlgClosure K Ω]

lemma canonical_tateEvaluation (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    tateEvaluation A ℓ n (PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ)) t) =
      Additive.ofMul (canonicalAction A (ℓ ^ n) (restriction A (ℓ ^ n) σ)
        (Additive.toMul (tateEvaluation A ℓ n t))) := by
  rw [canonicalAction_restriction]
  exact tateEvaluation_galois A ℓ n σ t

lemma canonical_transition (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (τ : divisionField (Ω := Ω) A (ℓ ^ (n + 1)) ≃ₐ[K] divisionField (Ω := Ω) A (ℓ ^ (n + 1)))
    (x : torsionSubgroup A Ω (ℓ ^ (n + 1))) :
    transition A ℓ n (canonicalAction A (ℓ ^ (n + 1)) τ x) =
      canonicalAction A (ℓ ^ n) (levelRestriction A ℓ n τ) (transition A ℓ n x) := by
  obtain ⟨σ, rfl⟩ := restriction_surjective A (ℓ ^ (n + 1)) τ
  rw [levelRestriction_absolute, canonicalAction_restriction, canonicalAction_restriction]
  exact transition_galois A ℓ n σ x

end ActualClosedDivisionKernel

#check @ActualClosedDivisionKernel.canonical_tateEvaluation
#check @ActualClosedDivisionKernel.canonical_transition
#print axioms ActualClosedDivisionKernel.canonical_tateEvaluation
#print axioms ActualClosedDivisionKernel.canonical_transition
