import Mathlib

/-!
# Leaf T1 reduces to finite `R`-algebras (Zariski's Main Theorem)

`PkgI2.PurityBranchLocus` is copied verbatim from `ZInQKernel/HDecomp/Objects.lean`.
`PurityBranchLocusFinite` is the same statement for `R → S` *finite* (module-finite), without the
(then automatic) quasi-finiteness hypothesis: the classical Zariski–Nagata form (finite cover of a
regular scheme by a normal one).  Mathlib's Zariski Main Theorem
(`Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective`) gives a module-finite
`S' ⊆ S` and `r ∈ S' \ q` with `S'[1/r] = S[1/r]`; then `S'_{q ∩ S'} ≅ S_q` as `R`-algebras and the
hypotheses transfer.
-/

open IsLocalRing

universe u

namespace PkgI2

/-- Copied verbatim from `ZInQKernel/HDecomp/Objects.lean`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

end PkgI2

namespace TPurity2

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- From `S'[1/r] = S[1/r]`: every `x ∈ S` has `r^N x ∈ S'`. -/
theorem exists_pow_mul_mem (S' : Subalgebra R S) (r : S')
    (hbij : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) (x : S) :
    ∃ N : ℕ, (r : S) ^ N * x ∈ S' := by
  obtain ⟨y, hy⟩ := hbij.2 (algebraMap S (Localization.Away (S'.val.toRingHom r)) x)
  obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) y
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq_mul, ← map_mul,
    IsLocalization.eq_iff_exists (Submonoid.powers (S'.val.toRingHom r))] at hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hy
  refine ⟨k + n, ?_⟩
  have e : (r : S) ^ (k + n) * x = (r : S) ^ k * (a : S) := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val, map_pow] at hk
    rw [hk, pow_add]; ring
  rw [e]
  exact S'.mul_mem (S'.pow_mem r.2 k) a.2

/-- The localization of `S` at `P ∌ r` is the localization of `S'` at `P ∩ S'`. -/
theorem isLocalization_atPrime_of_pow (S' : Subalgebra R S) (r : S')
    (hpow : ∀ x : S, ∃ N : ℕ, (r : S) ^ N * x ∈ S')
    (P : Ideal S) [P.IsPrime] (hr : (r : S) ∉ P) :
    IsLocalization (P.comap (algebraMap S' S)).primeCompl (Localization.AtPrime P) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime P) (⟨(s : S), hs⟩ : P.primeCompl)
  · intro z
    obtain ⟨x, ⟨t, ht⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    obtain ⟨N, hN⟩ := hpow x
    obtain ⟨M, hM⟩ := hpow t
    have hden : (⟨(r : S) ^ N * ((r : S) ^ M * t), S'.mul_mem (S'.pow_mem r.2 N) hM⟩ : S') ∈
        (P.comap (algebraMap S' S)).primeCompl := by
      show (r : S) ^ N * ((r : S) ^ M * t) ∉ P
      intro h
      rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance N h)
      · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
        · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance M h)
        · exact ht h
    refine ⟨⟨⟨(r : S) ^ N * x, hN⟩ * ⟨(r : S) ^ M, S'.pow_mem r.2 M⟩, ⟨_, hden⟩⟩, ?_⟩
    show IsLocalization.mk' (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl) *
        algebraMap S (Localization.AtPrime P) ((r : S) ^ N * ((r : S) ^ M * t)) =
      algebraMap S (Localization.AtPrime P) ((r : S) ^ N * x * (r : S) ^ M)
    have key := IsLocalization.mk'_spec (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl)
    simp only at key
    calc _ = (IsLocalization.mk' (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl) *
          algebraMap S (Localization.AtPrime P) t) *
          algebraMap S (Localization.AtPrime P) ((r : S) ^ N * (r : S) ^ M) := by
            rw [show (r : S) ^ N * ((r : S) ^ M * t) = t * ((r : S) ^ N * (r : S) ^ M) by ring,
              map_mul]; ring
      _ = _ := by rw [key, ← map_mul]; congr 1; ring
  · intro a b hab
    simp only [IsScalarTower.algebraMap_apply S' S (Localization.AtPrime P)] at hab
    obtain ⟨⟨s, hs⟩, hsab⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hab
    obtain ⟨M, hM⟩ := hpow s
    refine ⟨⟨⟨(r : S) ^ M * s, hM⟩, ?_⟩, ?_⟩
    · show (r : S) ^ M * s ∉ P
      intro h
      rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance M h)
      · exact hs h
    · apply Subtype.ext
      show (r : S) ^ M * s * a = (r : S) ^ M * s * b
      rw [mul_assoc, mul_assoc]
      exact congrArg (fun y => (r : S) ^ M * y) hsab

/-- `S'_{P ∩ S'} ≅ S_P` as `R`-algebras when `r ∉ P`. -/
noncomputable def locEquiv (S' : Subalgebra R S) (r : S')
    (hpow : ∀ x : S, ∃ N : ℕ, (r : S) ^ N * x ∈ S') (P : Ideal S) [P.IsPrime] (hr : (r : S) ∉ P) :
    Localization.AtPrime (P.comap (algebraMap S' S)) ≃ₐ[R] Localization.AtPrime P :=
  haveI := isLocalization_atPrime_of_pow S' r hpow P hr
  haveI : IsScalarTower R S' (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  (IsLocalization.algEquiv (P.comap (algebraMap S' S)).primeCompl
    (Localization.AtPrime (P.comap (algebraMap S' S))) (Localization.AtPrime P)).restrictScalars R

theorem atPrime_congr_regular {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : IsRegularLocalRing (Localization.AtPrime I) ↔
      IsRegularLocalRing (Localization.AtPrime J) := by
  subst h; rfl

theorem atPrime_congr_dim {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : ringKrullDim (Localization.AtPrime I) = ringKrullDim (Localization.AtPrime J) := by
  subst h; rfl

theorem atPrime_congr_unram {A : Type u} [CommRing A] [Algebra R A] {I J : Ideal A} [I.IsPrime]
    [J.IsPrime] (h : I = J) : Algebra.IsUnramifiedAt R I ↔ Algebra.IsUnramifiedAt R J := by
  subst h; rfl

/-- The leaf for module-finite algebras (quasi-finiteness is then automatic). -/
def PurityBranchLocusFinite : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-- **T1 reduces to finite `R`-algebras** (via Zariski's Main Theorem). -/
theorem purityBranchLocus_of_finite (h : PurityBranchLocusFinite.{u}) :
    PkgI2.PurityBranchLocus.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hqf hdim h1 hunr
  obtain ⟨S', hfg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) q
  have hpow := exists_pow_mul_mem S' r hbij
  have : Module.Finite R S' := Module.Finite.iff_fg.mpr hfg
  set q' : Ideal S' := q.comap (algebraMap S' S) with hq'
  let e := locEquiv S' r hpow q hrq
  have hcomap : q'.comap (algebraMap R S') = q.comap (algebraMap R S) := by
    ext x; rfl
  have hdomq : IsDomain (Localization.AtPrime q') :=
    Function.Injective.isDomain (e : Localization.AtPrime q' →+* Localization.AtPrime q)
      e.injective
  have hicq : IsIntegrallyClosed (Localization.AtPrime q') :=
    IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  have hdimq : ringKrullDim (Localization.AtPrime q') = ringKrullDim (Localization.AtPrime q) :=
    ringKrullDim_eq_of_ringEquiv e.toRingEquiv
  have key : Algebra.IsEtaleAt R q' := by
    refine h R S' q' ((atPrime_congr_regular hcomap).mpr hreg) hdomq hicq
      (by rw [hdimq, hdim, atPrime_congr_dim hcomap]) (by rw [hdimq]; exact h1) ?_
    intro q'' _ hle hht
    have hrq'' : r ∉ q'' := fun hr => hrq (hle hr)
    -- a prime `P` of `S` over `q''`
    let iso := RingEquiv.ofBijective (Localization.awayMap S'.val.toRingHom r) hbij
    have hunit : IsUnit (algebraMap S' (Localization.AtPrime q'') r) :=
      IsLocalization.map_units (Localization.AtPrime q'') (⟨r, hrq''⟩ : q''.primeCompl)
    let ψ : S →+* Localization.AtPrime q'' :=
      (Localization.awayLift (algebraMap S' (Localization.AtPrime q'')) r hunit).comp
        (iso.symm.toRingHom.comp (algebraMap S (Localization.Away (S'.val.toRingHom r))))
    have hψ : ∀ a : S', ψ (a : S) = algebraMap S' (Localization.AtPrime q'') a := by
      intro a
      have h1 : iso (algebraMap S' (Localization.Away r) a) =
          algebraMap S (Localization.Away (S'.val.toRingHom r)) (a : S) := by
        show Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) a) = _
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
        rfl
      have h2 : iso.symm (algebraMap S (Localization.Away (S'.val.toRingHom r)) (a : S)) =
          algebraMap S' (Localization.Away r) a := by
        rw [← h1, RingEquiv.symm_apply_apply]
      show Localization.awayLift _ r hunit (iso.symm _) = _
      rw [h2, Localization.awayLift, IsLocalization.Away.lift_eq]
    let P : Ideal S := (maximalIdeal (Localization.AtPrime q'')).comap ψ
    have hPprime : P.IsPrime := Ideal.comap_isPrime ψ _
    have hPc : P.comap (algebraMap S' S) = q'' := by
      ext a
      show ψ (a : S) ∈ maximalIdeal _ ↔ a ∈ q''
      rw [hψ]
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q'') q'' a
    have hrP : (r : S) ∉ P := by
      show ψ (r : S) ∉ maximalIdeal _
      rw [hψ]
      exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm hunit
    have hPle : P ≤ q := by
      intro x hx
      obtain ⟨N, hN⟩ := hpow x
      have : (⟨(r : S) ^ N * x, hN⟩ : S') ∈ q'' := by
        rw [← hPc]
        show ψ ((r : S) ^ N * x) ∈ maximalIdeal _
        rw [map_mul]
        exact Ideal.mul_mem_left _ _ hx
      have hq : (r : S) ^ N * x ∈ q := hle this
      rcases Ideal.IsPrime.mem_or_mem inferInstance hq with h' | h'
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance N h') hrq
      · exact h'
    let eP := locEquiv S' r hpow P hrP
    have hPht : P.height = 1 := by
      have a1 := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
      have a2 := IsLocalization.AtPrime.ringKrullDim_eq_height (P.comap (algebraMap S' S))
        (Localization.AtPrime (P.comap (algebraMap S' S)))
      have a3 := ringKrullDim_eq_of_ringEquiv eP.toRingEquiv
      have a4 : (P.comap (algebraMap S' S)).height = 1 := by rw [hPc]; exact hht
      rw [a4] at a2
      rw [a2, a1] at a3
      exact_mod_cast a3.symm
    have := hunr P hPle hPht
    have hU : Algebra.FormallyUnramified R (Localization.AtPrime (P.comap (algebraMap S' S))) :=
      Algebra.FormallyUnramified.of_equiv eP.symm
    exact (atPrime_congr_unram hPc).mp hU
  exact Algebra.FormallyEtale.of_equiv e

end TPurity2

#print axioms TPurity2.purityBranchLocus_of_finite
