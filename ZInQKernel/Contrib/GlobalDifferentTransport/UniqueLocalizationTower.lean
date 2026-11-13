/-
# Unique primes descend through an actual integral tower

The proof lifts each intermediate prime through the integral faithful upper
extension, then uses the proved unique-prime statement at the top. It does not
assume uniqueness at the intermediate level.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.UniqueLocalization

/-!
# Intermediate unique-prime localization

This applies to the proposed `F ⊆ U ⊆ E ⊆ M` route only after the actual field
and ring inclusions and scalar towers have been constructed. It is a proved
supplier for their unique-prime/finiteness step, not a proof of that whole diagram.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace GlobalDifferentTransport

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.IsIntegral S T] [FaithfulSMul S T]
  (p : Ideal R) [p.IsPrime] (P : Ideal T) [P.IsPrime] [P.LiesOver p]

omit [p.IsPrime] in
/-- The unique-prime property at the top of a faithful integral tower proves it at the
intermediate ring, with the actual contracted prime. -/
theorem primesOver_unique_descends
    (hUnique : Ideal.primesOver p T = {P}) :
    Ideal.primesOver p S = {P.under S} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rintro q ⟨hq, hqp⟩
  let := hq
  let := hqp
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Ideal.primesOver q T))
  let : Q.1.IsPrime := Q.2.1
  let : Q.1.LiesOver q := Q.2.2
  let : Q.1.LiesOver p := Ideal.LiesOver.trans Q.1 q p
  have hQ : Q.1 ∈ Ideal.primesOver p T := ⟨inferInstance, inferInstance⟩
  rw [hUnique, Set.mem_singleton_iff] at hQ
  exact (Ideal.over_def Q.1 q).trans (congrArg (Ideal.under S) hQ)

variable [Module.Finite R S]

/-- An actual finite intermediate algebra has a genuinely finite single-prime localization
over the localized base when uniqueness is proved at the integral upper field. -/
theorem moduleFinite_intermediate_atPrime_of_unique_top
    (hUnique : Ideal.primesOver p T = {P}) :
    let _ := Localization.AtPrime.algebraOfLiesOver p (P.under S)
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime (P.under S)) :=
  moduleFinite_atPrime_of_unique p (P.under S) (primesOver_unique_descends p P hUnique)

end GlobalDifferentTransport
