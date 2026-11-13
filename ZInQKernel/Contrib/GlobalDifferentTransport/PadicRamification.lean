/-
# Ramification on the actual padic scalar model

Only the base-change through the proved native integer-ring equivalence is new.
The global/completed ramification comparison is consumed from the immutable
NumberField/Ramification producers, not reproved. The integer algebra map here
is the actual inverse native equivalence followed by completion.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.PadicCompletionModel

/-!
# Same genuine ramification index after the Zp integer-base identification

The correct mapped maximal ideal is identified using the native local integer
ring equivalence and the exact canonical scalar square. The normalized global
ramification equality then applies unchanged, including primes above 2.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField IsLocalRing
open scoped NumberField GlobalDifferentTransportCompletion GlobalDifferentTransportPadicCompletion

namespace GlobalDifferentTransport

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- Faithfulness of the actual Zp-to-completed-integers map, derived from its named factors. -/
theorem faithfulSMul_padicCompletionIntegers :
    FaithfulSMul ℤ_[completionPrime v] (w.adicCompletionIntegers L) := by
  rw [faithfulSMul_iff_algebraMap_injective, algebraMap_padicCompletionIntegersAlgebra]
  exact (completionIntegersRingHom_injective ℚ L v w).comp
    (rationalCompletionIntegersPadicEquiv v).symm.injective

/-- The actual completed maximal ideal lies over the actual Zp maximal ideal. -/
theorem maximalIdeal_padicCompletionIntegers_liesOver :
    (maximalIdeal (w.adicCompletionIntegers L)).LiesOver (maximalIdeal ℤ_[completionPrime v]) := by
  rw [Ideal.liesOver_iff, Ideal.under_def, algebraMap_padicCompletionIntegersAlgebra,
    ← Ideal.comap_comap, comap_maximalIdeal_completionIntegersRingHom]
  have h : (maximalIdeal (v.adicCompletionIntegers ℚ)).comap
      (rationalCompletionIntegersPadicEquiv v).symm.toAlgEquiv.toRingHom =
        maximalIdeal ℤ_[completionPrime v] := by
    change (maximalIdeal (v.adicCompletionIntegers ℚ)).comap
      (rationalCompletionIntegersPadicEquiv v).toAlgEquiv.toRingEquiv.symm = _
    rw [Ideal.comap_symm, IsLocalRing.map_ringEquiv_maximalIdeal]
  exact h.symm

scoped[GlobalDifferentTransportPadicCompletion] attribute [instance]
  GlobalDifferentTransport.faithfulSMul_padicCompletionIntegers
  GlobalDifferentTransport.maximalIdeal_padicCompletionIntegers_liesOver

/-- The actual image of the Zp maximal ideal is the same ideal as the image of the canonical
completed-base maximal ideal. This identifies the precise ideal used by ramification. -/
theorem map_maximalIdeal_padicCompletionIntegers :
    (maximalIdeal ℤ_[completionPrime v]).map
        (algebraMap ℤ_[completionPrime v] (w.adicCompletionIntegers L)) =
      (maximalIdeal (v.adicCompletionIntegers ℚ)).map
        (algebraMap (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) := by
  rw [algebraMap_padicCompletionIntegersAlgebra, algebraMap_completionIntegersAlgebra,
    ← Ideal.map_map]
  change ((maximalIdeal ℤ_[completionPrime v]).map
      (rationalCompletionIntegersPadicEquiv v).symm.toAlgEquiv.toRingEquiv).map
        (completionIntegersRingHom ℚ L v w) = _
  rw [IsLocalRing.map_ringEquiv_maximalIdeal]

/-- Changing the integer base by its actual native Zp equivalence preserves the actual
completed-ring ramification index. No global equality is reproved here. -/
theorem ramificationIdx_padicBase_eq_completedBase :
    (maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx ℤ_[completionPrime v] =
      (maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx (v.adicCompletionIntegers ℚ) := by
  let := faithfulSMul_padicCompletionIntegers L v w
  let : Module.IsTorsionFree ℤ_[completionPrime v] (w.adicCompletionIntegers L) := inferInstance
  let := maximalIdeal_padicCompletionIntegers_liesOver L v w
  have hz : maximalIdeal ℤ_[completionPrime v] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hv : maximalIdeal (v.adicCompletionIntegers ℚ) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hzmap : (maximalIdeal ℤ_[completionPrime v]).map
      (algebraMap ℤ_[completionPrime v] (w.adicCompletionIntegers L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hz
  have hvmap : (maximalIdeal (v.adicCompletionIntegers ℚ)).map
      (algebraMap (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hv
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (maximalIdeal ℤ_[completionPrime v]) (maximalIdeal (w.adicCompletionIntegers L)) hzmap,
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (maximalIdeal (v.adicCompletionIntegers ℚ)) (maximalIdeal (w.adicCompletionIntegers L)) hvmap,
    map_maximalIdeal_padicCompletionIntegers L v w]

/-- The actual completed DVR's ramification over the actual Zp model equals the original
integer-ring prime's global index. The immutable normalized theorem is consumed unchanged. -/
theorem ramificationIdx_padicNumberFieldCompletion_eq :
    (maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx ℤ_[completionPrime v] =
      w.asIdeal.ramificationIdx ℤ :=
  (ramificationIdx_padicBase_eq_completedBase L v w).trans
    (ramificationIdx_numberFieldCompletion_eq L v w)

end GlobalDifferentTransport
