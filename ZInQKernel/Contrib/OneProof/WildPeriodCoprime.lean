import ZInQKernel.Contrib.OneProof.SZRaynaud
import ZInQKernel.Contrib.OneProof.WildPeriodCoprimeCore

namespace SZRaynaud

/-- **ON THE SPOT (provenance (c)).** Restrict to the normal closure of a finite
field of definition for the point. The power of the wild automorphism obtained by
taking the prime-to-`ℓ` part of its order there has `ℓ`-power order on this field.
Averaging displacements shows that this power already fixes the field, since
`ℓ` is invertible. Its exponent is therefore a period of the point prime to `ℓ`. -/
theorem wildPeriodCoprime_proof : WildPeriodCoprime := by
  intro K _ O _ Ω _ _ _ w hw A ℓ hℓ hℓO σ _ hwild n x _
  obtain ⟨N, hN, hfix⟩ := WildPeriod.exists_coprime_period hw A hℓ.out hℓO hwild x
  exact ⟨N, hN.pow_right n, hfix⟩

/-- The wild inertia consequence of semistable unipotence, with the period argument
discharged in Lean. -/
theorem elliot_of_semistableUnipotent_of_period_proof
    (hU : ReductSplit.SemistableUnipotent) : ElliotWildInertiaTrivial :=
  elliot_of_semistableUnipotent hU wildPeriodCoprime_proof

#print axioms wildPeriodCoprime_proof
#print axioms elliot_of_semistableUnipotent_of_period_proof

end SZRaynaud
