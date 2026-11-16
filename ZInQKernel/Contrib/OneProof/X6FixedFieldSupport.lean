import ZInQKernel.Contrib.CloudB3SC6FixedFields.PointFibreInvariance
import ZInQKernel.Contrib.CloudB3SC6FixedFields.FiniteAutomorphisms

/-! # Supporting results for the X6 fixed-field converse

This entry point exposes geometric-point detection, coordinate-germ invariance,
and the finite-automorphism criterion. It is not an unconditional proof of
`HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField` and introduces no new
printed leaf. In particular, the concrete X6 degree bound, four sign actions,
and existential moduli witness are not supplied here.
-/

namespace CloudB3SC6FixedFieldSupport

/-- The abstract final step: four distinct automorphisms of a finite extension
of degree at most four detect precisely the elements of its base field. -/
theorem fixed_elements_of_four_automorphisms
    (F K : Type*) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (σ : Fin 4 → K ≃ₐ[F] K) (hσ : Function.Injective σ)
    (hdegree : Module.finrank F K ≤ 4) (x : K) :
    (∀ i, σ i x = x) ↔ x ∈ Set.range (algebraMap F K) :=
  CloudB3SC6FixedFields.fixed_iff_mem_base_of_four_automorphisms F K σ hσ hdegree x

end CloudB3SC6FixedFieldSupport
