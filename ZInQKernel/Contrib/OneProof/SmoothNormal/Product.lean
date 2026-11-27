import Mathlib

/-!
# Noetherian normal rings are finite products of normal domains

Let `R` be a commutative noetherian ring all of whose localizations at prime ideals are
integrally closed domains. Then `R` is isomorphic to a finite product of integrally closed
domains, namely the quotients `R ⧸ p` by its finitely many minimal primes `p`. This is the last
sentence of EGA IV₂ (5.13.5) (Publ. Math. IHÉS 24 (1965), p. 133): "Si A est noethérien et
normal, A est composé direct d'un nombre fini d'anneaux intègres et intégralement clos
(I, 5.1.4)"; it is proved here.

Outline.
* For a prime `m` with `R_m` a domain, the kernel of `R → R_m` is a prime ideal contained in
  every prime ideal inside `m`; hence it is the unique minimal prime of `R` inside `m`.
* Consequently distinct minimal primes are comaximal and the minimal primes intersect to zero,
  so the Chinese remainder theorem gives `R ≃ ∏ p, R ⧸ p`.
* For a minimal prime `p` and a prime `P` of `R ⧸ p` with preimage `m` in `R`, the localization
  `(R ⧸ p)_P` is a localization of `R` at `m`, hence integrally closed. A domain all of whose
  localizations at maximal ideals are integrally closed is integrally closed.
-/

set_option autoImplicit false

namespace Y3Buzzard.SmoothNormal

section Lemmas

variable {R : Type} [CommRing R]

/-- The kernel of `R → R_m` lies in every prime ideal contained in `m`. -/
theorem ker_algebraMap_le {m q : Ideal R} [m.IsPrime] (hq : q.IsPrime) (hqm : q ≤ m) :
    RingHom.ker (algebraMap R (Localization.AtPrime m)) ≤ q := by
  intro x hx
  rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff m.primeCompl] at hx
  obtain ⟨⟨s, hs⟩, hsx⟩ := hx
  have hmem : s * x ∈ q := by
    rw [show s * x = 0 from hsx]
    exact q.zero_mem
  rcases hq.mem_or_mem hmem with h | h
  · exact absurd (hqm h) hs
  · exact h

/-- If `R_m` is a domain, a minimal prime contained in `m` is the kernel of `R → R_m`. -/
theorem eq_ker_of_mem_minimalPrimes {p m : Ideal R} [m.IsPrime]
    [IsDomain (Localization.AtPrime m)] (hp : p ∈ minimalPrimes R) (hpm : p ≤ m) :
    p = RingHom.ker (algebraMap R (Localization.AtPrime m)) := by
  have hp' : Minimal (fun q : Ideal R => q.IsPrime ∧ ⊥ ≤ q) p := hp
  have hle := ker_algebraMap_le hp'.1.1 hpm
  exact le_antisymm (hp'.2 ⟨RingHom.ker_isPrime _, bot_le⟩ hle) hle

/-- If all localizations at primes are domains, distinct minimal primes are comaximal. -/
theorem isCoprime_of_mem_minimalPrimes
    (h : ∀ (q : Ideal R) (_ : q.IsPrime), IsDomain (Localization.AtPrime q))
    {p p' : Ideal R} (hp : p ∈ minimalPrimes R) (hp' : p' ∈ minimalPrimes R) (hne : p ≠ p') :
    IsCoprime p p' := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hpp
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hpp
  have := hm.isPrime
  have := h m hm.isPrime
  exact hne ((eq_ker_of_mem_minimalPrimes hp (le_sup_left.trans hle)).trans
    (eq_ker_of_mem_minimalPrimes hp' (le_sup_right.trans hle)).symm)

/-- If all localizations at primes are domains, the minimal primes intersect to zero. -/
theorem iInf_minimalPrimes_eq_bot
    (h : ∀ (q : Ideal R) (_ : q.IsPrime), IsDomain (Localization.AtPrime q)) :
    ⨅ p : minimalPrimes R, (p : Ideal R) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  refine eq_zero_of_localization x fun J hJ => ?_
  have := hJ.isPrime
  have := h J hJ.isPrime
  obtain ⟨p, hp, hpJ⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ J)
  have hxp : x ∈ p := (Submodule.mem_iInf _).mp hx ⟨p, hp⟩
  rw [eq_ker_of_mem_minimalPrimes hp hpJ] at hxp
  exact RingHom.mem_ker.mp hxp

/-- For a minimal prime `p` and a prime `P` of `R ⧸ p` whose preimage `m` in `R` has `R_m` a
domain, the localization `(R ⧸ p)_P` is a localization of `R` at `m`. -/
theorem isLocalization_atPrime_quotient {p : Ideal R} (hp : p ∈ minimalPrimes R)
    (P : Ideal (R ⧸ p)) [P.IsPrime]
    [IsDomain (Localization.AtPrime (P.comap (Ideal.Quotient.mk p)))] :
    IsLocalization (P.comap (Ideal.Quotient.mk p)).primeCompl (Localization.AtPrime P) := by
  set m := P.comap (Ideal.Quotient.mk p)
  have hpm : p ≤ m := fun x hx => by
    show Ideal.Quotient.mk p x ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.zero_mem
  have hker := eq_ker_of_mem_minimalPrimes hp hpm
  have halg : ∀ x : R, algebraMap R (Localization.AtPrime P) x =
      algebraMap (R ⧸ p) (Localization.AtPrime P) (Ideal.Quotient.mk p x) := fun x => by
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (Localization.AtPrime P),
      Ideal.Quotient.algebraMap_eq]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · rw [halg]
    exact IsLocalization.map_units (Localization.AtPrime P)
      (⟨Ideal.Quotient.mk p y, y.2⟩ : P.primeCompl)
  · obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj P.primeCompl z
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨⟨a', ⟨b', hb⟩⟩, ?_⟩
    rw [halg, halg]
    exact hab
  · rw [halg, halg] at hxy
    obtain ⟨⟨c, hc⟩, hcxy⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hxy
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : c' * (x - y) ∈ RingHom.ker (algebraMap R (Localization.AtPrime m)) := by
      rw [← hker, ← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, mul_sub, sub_eq_zero]
      exact hcxy
    rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff m.primeCompl] at h1
    obtain ⟨⟨s, hs⟩, hs0⟩ := h1
    refine ⟨⟨s * c', m.primeCompl.mul_mem hs hc⟩, ?_⟩
    show s * c' * x = s * c' * y
    rw [← sub_eq_zero, ← mul_sub, mul_assoc]
    exact hs0

/-- For a minimal prime `p`, every localization of `R ⧸ p` at a prime is integrally closed. -/
theorem isIntegrallyClosed_atPrime_quotient
    (h : ∀ (q : Ideal R) (_ : q.IsPrime), IsDomain (Localization.AtPrime q) ∧
      IsIntegrallyClosed (Localization.AtPrime q))
    {p : Ideal R} (hp : p ∈ minimalPrimes R) (P : Ideal (R ⧸ p)) [P.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime P) := by
  have := (h (P.comap (Ideal.Quotient.mk p)) inferInstance).1
  have := (h (P.comap (Ideal.Quotient.mk p)) inferInstance).2
  have := isLocalization_atPrime_quotient hp P
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv (P.comap (Ideal.Quotient.mk p)).primeCompl
      (Localization.AtPrime (P.comap (Ideal.Quotient.mk p)))
      (Localization.AtPrime P)).toRingEquiv

/-- For a minimal prime `p`, the domain `R ⧸ p` is integrally closed. -/
theorem isIntegrallyClosed_quotient
    (h : ∀ (q : Ideal R) (_ : q.IsPrime), IsDomain (Localization.AtPrime q) ∧
      IsIntegrallyClosed (Localization.AtPrime q))
    {p : Ideal R} (hp : p ∈ minimalPrimes R) [p.IsPrime] :
    IsIntegrallyClosed (R ⧸ p) :=
  IsIntegrallyClosed.of_localization_maximal fun P _ _ =>
    isIntegrallyClosed_atPrime_quotient h hp P

end Lemmas

/-- A commutative noetherian ring all of whose localizations at primes are integrally closed
domains is a finite product of integrally closed domains (the quotients by its minimal primes). -/
theorem exists_piEquiv_of_normal (R : Type) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) (_ : p.IsPrime), IsDomain (Localization.AtPrime p) ∧
      IsIntegrallyClosed (Localization.AtPrime p)) :
    ∃ (n : ℕ) (D : Fin n → Type) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsDomain (D i))
      (_ : ∀ i, IsIntegrallyClosed (D i)), Nonempty (R ≃+* ∀ i, D i) := by
  have : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  have hdom : ∀ (q : Ideal R) (_ : q.IsPrime), IsDomain (Localization.AtPrime q) :=
    fun q hq => (h q hq).1
  let f : minimalPrimes R → Ideal R := fun q => q.1
  have hcop : Pairwise (Function.onFun IsCoprime f) := fun i j hij =>
    isCoprime_of_mem_minimalPrimes hdom i.2 j.2 fun hh => hij (Subtype.ext hh)
  let e := Finite.equivFin (minimalPrimes R)
  refine ⟨Nat.card (minimalPrimes R), fun b => R ⧸ f (e.symm b), fun _ => inferInstance,
    fun b => ?_, fun b => ?_, ⟨?_⟩⟩
  · have : (f (e.symm b)).IsPrime := IsMinimalPrime.isPrime (e.symm b).2
    show IsDomain (R ⧸ f (e.symm b))
    infer_instance
  · have : (f (e.symm b)).IsPrime := IsMinimalPrime.isPrime (e.symm b).2
    show IsIntegrallyClosed (R ⧸ f (e.symm b))
    exact isIntegrallyClosed_quotient h (e.symm b).2
  · exact (RingEquiv.quotientBot R).symm.trans
      ((Ideal.quotEquivOfEq (iInf_minimalPrimes_eq_bot hdom).symm).trans
        ((Ideal.quotientInfRingEquivPiQuotient f hcop).trans
          (RingEquiv.piCongrLeft' (fun i => R ⧸ f i) e)))

end Y3Buzzard.SmoothNormal
