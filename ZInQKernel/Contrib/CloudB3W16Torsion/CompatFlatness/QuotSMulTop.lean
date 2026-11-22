/-
CloudB3 Worker16 H102 flatness compatibility helpers (2026-11-16).
Quotient scalar-tower and finiteness proofs adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M.Sol.S_IsLocalRing_isRegular_of_systemOfParameters, No4PatchingCore's
isScalarTower_quotient_span_singleton and moduleFinite_quotient_span_singleton.
Apache-2.0; source notices, credits, and LICENSE are preserved in
../Vendor/AnthropicFLT/{NOTICE.upstream,ATTRIBUTION.upstream.md,LICENSE}.
These are ordinary theorems, not new global instances or changes to the source export types.
-/
import Mathlib

namespace ZInQ.Contrib.CloudB3W16Torsion.CompatFlatness

open RingTheory

/-- The two natural scalar actions on the quotient by `x • M` form a tower. -/
theorem isScalarTower_quotSMulTop {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (x : R) : IsScalarTower R (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl

/-- Finiteness of `M` descends to the quotient with its natural quotient-ring action. -/
theorem finite_quotSMulTop {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] (x : R) :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  letI := isScalarTower_quotSMulTop (M := M) x
  exact Module.Finite.of_restrictScalars_finite R _ _

end ZInQ.Contrib.CloudB3W16Torsion.CompatFlatness
