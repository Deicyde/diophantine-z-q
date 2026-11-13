/-
# A single-prime localization is finite only with a genuine uniqueness argument

The proof uses Mathlib's proved unique-prime denominator theorem in GoingUp.lean,
integrality of a finite algebra, and simultaneous localization of a finite module.
No finiteness of S_P over the base localization is assumed.
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Unique-prime base localization

If `S` is a finite integral-domain algebra over `R`, and `P` is the only prime
of `S` above `p`, then localizing `S` at `P` is the same simultaneous base
localization at the image of `p.primeCompl`. Therefore it is genuinely finite
over `R_p`. The unique-prime premise is not omitted when primes split.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

namespace GlobalDifferentTransport

variable {R S : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Module.Finite R S]
  (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]

omit [Module.Finite R S] in
/-- Elements from the base prime complement remain outside every prime lying over it. -/
theorem algebraMapSubmonoid_le_primeCompl :
    Algebra.algebraMapSubmonoid S p.primeCompl ≤ P.primeCompl := by
  rintro _ ⟨a, ha, rfl⟩
  exact fun h ↦ ha ((Ideal.mem_of_liesOver P p a).mpr h)

omit [P.IsPrime] [P.LiesOver p] in
/-- Under genuine uniqueness, every element outside `P` divides the image of some base element
outside `p`. A prime disjoint from the base complement would otherwise contradict uniqueness. -/
theorem exists_base_primeCompl_multiple
    (hUnique : Ideal.primesOver p S = {P}) (x : S) (hx : x ∉ P) :
    ∃ m ∈ Algebra.algebraMapSubmonoid S p.primeCompl, x ∣ m := by
  let : P.IsPrime := (show P ∈ Ideal.primesOver p S from by
    rw [hUnique]
    exact Set.mem_singleton P).1
  obtain ⟨r, hr, hdvd⟩ :=
    Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton hUnique x hx
  exact ⟨algebraMap R S r, ⟨r, hr, rfl⟩, hdvd⟩

/-- At a unique prime above `p`, the single-prime localization is the simultaneous localization
at the image of the base prime complement. This is the needed hypothesis for different localization. -/
theorem isLocalization_base_primeCompl_atPrime
    (hUnique : Ideal.primesOver p S = {P}) :
    IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime P) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (M := Algebra.algebraMapSubmonoid S p.primeCompl) (S := Localization.AtPrime P)
    P.primeCompl (algebraMapSubmonoid_le_primeCompl p P) ?_).mpr
  · infer_instance
  · intro x hx
    exact exists_base_primeCompl_multiple p P hUnique x hx

/-- The single-prime localization is genuinely finite over the localized base when the prime above
it is unique. The canonical localization algebra is used explicitly. -/
theorem moduleFinite_atPrime_of_unique
    (hUnique : Ideal.primesOver p S = {P}) :
    let _ := Localization.AtPrime.algebraOfLiesOver p P
    Module.Finite (Localization.AtPrime p) (Localization.AtPrime P) := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := isLocalization_base_primeCompl_atPrime p P hUnique
  exact Module.Finite.of_isLocalization R S p.primeCompl

end GlobalDifferentTransport
