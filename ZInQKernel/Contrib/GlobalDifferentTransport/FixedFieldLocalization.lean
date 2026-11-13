/-
# Actual decomposition fixed-field localization suppliers

These instantiate the pinned Mathlib Hilbert-theory proofs on a finite Galois
number field and combine their genuine unique-prime statement with the proved
base-localization finiteness criterion. They do not certify an F/E/U diagram.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.UniqueLocalization
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# The concrete decomposition fixed field

For `M/ℚ` finite Galois and an actual prime `P` of its ring of integers, set
`F = M^D` for the genuine stabilizer `D` of `P`, and `Q = P ∩ 𝓞 F`.
There is a unique prime above `Q`, and the selected single-prime localization
is genuinely a finite module over `(𝓞 F)_Q`. Nonzero-prime hypotheses are used
before declaring these localizations DVRs.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped NumberField Pointwise

namespace GlobalDifferentTransport

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  (P : Ideal (𝓞 M)) [P.IsPrime]

/-- The fixed field of the actual decomposition subgroup, not a new assumed intermediate field. -/
def decompositionFixedField : IntermediateField ℚ M :=
  FixedPoints.intermediateField (MulAction.stabilizer Gal(M/ℚ) P)

omit [IsGalois ℚ M] [P.IsPrime] in
/-- The ring of integers of the Galois field is finite over that of its actual fixed subfield. -/
theorem finite_decompositionFixedField_integers :
    Module.Finite (𝓞 (decompositionFixedField M P)) (𝓞 M) :=
  Module.Finite.right ℤ (𝓞 (decompositionFixedField M P)) (𝓞 M)

/-- The selected prime is the only prime above its contraction to the actual decomposition field. -/
theorem decompositionFixedField_primesOver :
    Ideal.primesOver (P.under (𝓞 (decompositionFixedField M P))) (𝓞 M) = {P} := by
  let F := decompositionFixedField M P
  change Ideal.primesOver (P.under (𝓞 F)) (𝓞 M) = {P}
  let : IsDecompositionField ℚ M P F := by
    change IsDecompositionField ℚ M P
      (FixedPoints.intermediateField (MulAction.stabilizer Gal(M/ℚ) P) : IntermediateField ℚ M)
    infer_instance
  let := finite_decompositionFixedField_integers M P
  exact IsDecompositionField.primesOver_eq_singleton ℚ M P F (𝓞 F) (P.under (𝓞 F))

/-- The actual single-prime localization is the simultaneous base localization at the fixed-field
prime complement. The false version without unique primes is not used. -/
theorem decompositionFixedField_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 M)
      (P.under (𝓞 (decompositionFixedField M P))).primeCompl) (Localization.AtPrime P) := by
  let := finite_decompositionFixedField_integers M P
  exact isLocalization_base_primeCompl_atPrime
    (P.under (𝓞 (decompositionFixedField M P))) P (decompositionFixedField_primesOver M P)

/-- The selected global prime gives a genuinely finite localized extension over the actual
localized decomposition field. No completion or completion isomorphism is assumed. -/
theorem decompositionFixedField_moduleFinite_localization :
    let _ := Localization.AtPrime.algebraOfLiesOver
      (P.under (𝓞 (decompositionFixedField M P))) P
    Module.Finite (Localization.AtPrime (P.under (𝓞 (decompositionFixedField M P))))
      (Localization.AtPrime P) := by
  let := finite_decompositionFixedField_integers M P
  exact moduleFinite_atPrime_of_unique
    (P.under (𝓞 (decompositionFixedField M P))) P (decompositionFixedField_primesOver M P)

omit [IsGalois ℚ M] [P.IsPrime] in
/-- A nonzero selected prime has nonzero contraction to the decomposition-field integer ring. -/
theorem decompositionFixedField_under_ne_bot (hP : P ≠ ⊥) :
    P.under (𝓞 (decompositionFixedField M P)) ≠ ⊥ := by
  let := finite_decompositionFixedField_integers M P
  intro hQ
  exact hP (Ideal.eq_bot_of_under_eq_bot hQ)

/-- The actual contracted prime in the decomposition field has global ramification index and
inertia degree one over `ℤ`. The source is instantiated with `ℤ/ℚ` explicitly, not `𝓞 ℚ`. -/
theorem decompositionFixedField_base_indices_eq_one (hP : P ≠ ⊥) :
    (P.under (𝓞 (decompositionFixedField M P))).ramificationIdx ℤ = 1 ∧
      (P.under (𝓞 (decompositionFixedField M P))).inertiaDeg ℤ = 1 := by
  let F := decompositionFixedField M P
  let p := P.under ℤ
  let Q := P.under (𝓞 F)
  let : IsDecompositionField ℚ M P F := by
    change IsDecompositionField ℚ M P
      (FixedPoints.intermediateField (MulAction.stabilizer Gal(M/ℚ) P) : IntermediateField ℚ M)
    infer_instance
  let : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hP
  let : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal
    (decompositionFixedField_under_ne_bot M P hP)
  change Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1
  exact ⟨IsDecompositionField.ramificationIdx_eq ℤ ℚ M p P F (𝓞 F) Q,
    IsDecompositionField.inertiaDeg_eq ℤ ℚ M p P F (𝓞 F) Q⟩

omit [IsGalois ℚ M] in
/-- At a nonzero selected prime, both actual localized rings are DVRs. -/
theorem decompositionFixedField_localizations_areDVR (hP : P ≠ ⊥) :
    IsDiscreteValuationRing
        (Localization.AtPrime (P.under (𝓞 (decompositionFixedField M P)))) ∧
      IsDiscreteValuationRing (Localization.AtPrime P) := by
  exact ⟨IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 (decompositionFixedField M P))
      (decompositionFixedField_under_ne_bot M P hP) _,
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 M) hP _⟩

end GlobalDifferentTransport
