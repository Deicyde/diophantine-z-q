/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The single-completion proofs used here are selected from TauCeti revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418.
The finite-dimensional completed-field argument is the proof of Mathlib
NumberTheory/NumberField/Completion/FinitePlace.lean, lines 442–452, specialized
directly to the affine base ring `ℤ` rather than silently identifying it with
`NumberField.RingOfIntegers ℚ`.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Ramification
public import ZInQKernel.Contrib.GlobalDifferentTransport.Approximation
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The exact number-field affine model

The base ring is `ℤ`, its fraction field is `ℚ`, and the target is the actual
ring of integers of `L`. The completed integer rings are the concrete adic
completion integer rings at the specified primes. No equivalence with a
different presentation of `ℤ_p`, or with the ring of integers of `ℚ`, is
assumed.

The ideal in the different-exponent comparisons below is explicitly the
**extended global different**, not an asserted completed relative different.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField GlobalDifferentTransportCompletion TensorProduct Valued

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The canonical completed field extension for the actual `ℤ ⊆ 𝓞 L` affine model is finite.
Surjectivity is proved by the closed range of a finite-dimensional tensor-product map,
not by assuming a local/global degree formula. -/
theorem moduleFinite_numberFieldCompletion :
    Module.Finite (v.adicCompletion ℚ) (w.adicCompletion L) := by
  let Φ : v.adicCompletion ℚ ⊗[ℚ] L →ₗ[v.adicCompletion ℚ] w.adicCompletion L :=
    (Algebra.TensorProduct.lift
      (Algebra.ofId (v.adicCompletion ℚ) (w.adicCompletion L))
      (Algebra.algHom ℚ L (w.adicCompletion L)) (fun _ _ ↦ mul_comm ..)).toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.ofId, Algebra.algHom]⟩
  have hclosed : IsClosed (Set.range Φ) := by
    rw [← Φ.coe_range]
    exact Φ.range.closed_of_finiteDimensional
  exact Module.Finite.of_surjective Φ
    (Set.range_eq_univ.mp (hclosed.closure_eq.symm.trans h_dense.closure_range))

/-- The genuine global different remains nonzero after extension to the completed integer ring. -/
theorem extended_globalDifferent_ne_bot :
    (differentIdeal ℤ (𝓞 L)).map
      (algebraMap (𝓞 L) (w.adicCompletionIntegers L)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

/-- For every exponent, the genuine global different has the same prime-power divisibility
as its explicitly extended ideal. This is not yet a comparison with the actual local different. -/
theorem pow_dvd_extended_globalDifferent_iff (n : ℕ) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n ∣
        (differentIdeal ℤ (𝓞 L)).map
          (algebraMap (𝓞 L) (w.adicCompletionIntegers L)) ↔
      w.asIdeal ^ n ∣ differentIdeal ℤ (𝓞 L) :=
  pow_dvd_map_adicCompletionIntegers_iff w _ n

/-- The coefficient of the extended global different is its genuine global coefficient. -/
theorem multiplicity_extended_globalDifferent_eq :
    multiplicity (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))
        ((differentIdeal ℤ (𝓞 L)).map
          (algebraMap (𝓞 L) (w.adicCompletionIntegers L))) =
      multiplicity w.asIdeal (differentIdeal ℤ (𝓞 L)) :=
  multiplicity_map_adicCompletionIntegers w _ differentIdeal_ne_bot

/-- The normalized valuation of an actual global integer is unchanged by completion.
This lifts the separately proved global normalization, without re-proving its arithmetic. -/
theorem valued_completed_globalInteger (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a : w.adicCompletion L) =
      w.intValuation a := by
  rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
    valuation_of_algebraMap]

/-- The actual completed-ring ramification index is the one in the global target. -/
theorem ramificationIdx_numberFieldCompletion_eq :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers ℚ) = w.asIdeal.ramificationIdx ℤ :=
  ramificationIdx_completionIntegers_eq ℚ L v w

end GlobalDifferentTransport
