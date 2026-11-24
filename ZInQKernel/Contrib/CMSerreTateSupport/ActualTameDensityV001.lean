import ZInQKernel.Contrib.CMSerreTateSupport.AmbientTameClosureV001
import ZInQKernel.Contrib.CMSerreTateSupport.FrobLift.CommutingFiniteV002

/-!
# An actual tame generator in the ambient Galois closure

The finite-layer construction yields ambient Krull density. This theorem
identifies its literal strict-displacement predicate with the actual wild
subgroup used by the finite-inertia consumer. No generator or density
hypothesis is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace ActualTameInertia

theorem exists_tameGeneratorDense (K : Type) [Field K] [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    ∃ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ ∧ FrobLift.TameGeneratorDense w τ := by
  obtain ⟨τ, hτ, hclosure⟩ := leaf_tame_generator_ambient_closure K O Ω w hw
  refine ⟨τ, hτ, ?_⟩
  unfold FrobLift.TameGeneratorDense
  intro σ hσ
  apply (closure_mono ?_) (hclosure hσ)
  rintro ρ ⟨k, π, hπ, hρ⟩
  exact ⟨k, π, (FrobLift.mem_wildSubgroup_iff w π).mpr hπ, hρ⟩

end ActualTameInertia

#check @ActualTameInertia.exists_tameGeneratorDense
#print axioms ActualTameInertia.exists_tameGeneratorDense
