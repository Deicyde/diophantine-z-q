import ZInQKernel.Contrib.Abhyankar.Normalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Canonical fraction-field maps after localization

Both localization-to-field maps extend the same coefficient map. Their
compatibility in a field tower is proved by localization extensionality;
it is not an added scalar-tower hypothesis in the final DVR statement.
-/

namespace ZInQ.Contrib.Abhyankar

/-- The canonical maps from a coefficient localization into the two fields
of a tower commute with the given field embedding. -/
theorem localization_field_scalarTower
    (S L M : Type*) [CommRing S] [IsDomain S] [Field L] [Field M]
    [Algebra S L] [IsFractionRing S L] [Algebra L M]
    [Algebra S M] [IsScalarTower S L M] [FaithfulSMul S M]
    (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime q) L] [IsScalarTower S (Localization.AtPrime q) L]
    [Algebra (Localization.AtPrime q) M] [IsScalarTower S (Localization.AtPrime q) M] :
    IsScalarTower (Localization.AtPrime q) L M := by
  let B := Localization.AtPrime q
  have h : (algebraMap L M).comp (algebraMap B L) = algebraMap B M := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext s
    change algebraMap L M (algebraMap B L (algebraMap S B s)) =
      algebraMap B M (algebraMap S B s)
    rw [← IsScalarTower.algebraMap_apply S B L,
      ← IsScalarTower.algebraMap_apply S B M, ← IsScalarTower.algebraMap_apply S L M]
  exact IsScalarTower.of_algebraMap_eq fun b ↦ (RingHom.congr_fun h b).symm

/-- The specified fraction field of a domain remains the fraction field of
its canonical localization at a prime. -/
theorem localization_isFractionRing
    (S L : Type*) [CommRing S] [IsDomain S] [Field L]
    [Algebra S L] [IsFractionRing S L] (q : Ideal S) [q.IsPrime]
    [Algebra (Localization.AtPrime q) L] [IsScalarTower S (Localization.AtPrime q) L] :
    IsFractionRing (Localization.AtPrime q) L :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl (Localization.AtPrime q) L

end ZInQ.Contrib.Abhyankar
