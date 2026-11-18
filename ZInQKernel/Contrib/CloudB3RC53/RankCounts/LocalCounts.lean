import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
import ZInQKernel.Contrib.OneProof.RC.Limits.Lemmas
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.QuadraticPlaces

/-!
# RankCounts: RC6's local place data from the genuine completions of `K`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4544–4582. For each rational
prime `p` and each prime `w` of `𝓞 K` above `p`, the genuine completion `K_w = w.adicCompletion K`
is a finite extension of `ℚ_p` of degree `e(w|p) f(w|p)` (`finrank_qp`, from Tau Ceti's
`finrank_adicCompletion` and Mathlib's `ℚ_p ≃ ℚ_v`). `placesList K cond condDim p` is the list of
RC6 `PlaceData` of these places: `d_w = [K_w : ℚ₂]` (or `0` for odd `p`), `h^i(K_w, W)` for
`W = 𝔽₂²` trivial over Mathlib's continuous cohomology, the local condition `cond w` and its
residual dimension `condDim w`. For it, RC6's fields `places_length` (one entry per prime above
`p`), `places_deg` (`∑ d_w ≤ 2`) and `places_counts` (from the PRINT leaves Milne ADT I.2.3, I.2.8
and Elliot's table, ELLIOT) are PROVED.

Kinds: PROVED (the table value of each condition is the ELLIOT input `hcond`; the derived local
conditions themselves are not defined in Lean). Downstream, `LocalConditions.hcond_genuine` proves
`hcond` for condition dimensions computed from genuine cohomology, given the old-Kummer dimension
input `kummerDim = 4 + d_w`.
-/

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open ZInQ.Manuscript.RC.Limits

variable (K : Type) [Field K] [NumberField K]
/-- The height-one prime of `ℤ` at the rational prime `p`. -/
abbrev vP (p : Nat.Primes) : HeightOneSpectrum ℤ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
instance instFactPrimeNatPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩
/-- the ring isomorphism `ℚ_[p] ≃ ℚ_v` -/
def qpEquiv (p : Nat.Primes) : ℚ_[p] ≃+* (vP p).adicCompletion ℚ :=
  letI : Algebra ℚ ((vP p).adicCompletion ℚ) := HeightOneSpectrum.instAlgebraAdicCompletion ℤ ℚ _
  (Padic.adicCompletionEquiv ℤ p).toRingEquiv
/-- `K_w` as a `ℚ_[p]`-algebra, through `ℚ_[p] ≃ ℚ_v → K_w` (the extension of completions of
Tau Ceti's `AdicCompletionExtension`). -/
@[instance_reducible] def qpAlg (p : Nat.Primes) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    Algebra ℚ_[p] (w.adicCompletion K) :=
  ((algebraMap ((vP p).adicCompletion ℚ) (w.adicCompletion K)).comp
    (qpEquiv p).toRingHom).toAlgebra
/-- **`[K_w : ℚ_p] = e(w|p) f(w|p)`** (Tau Ceti's `finrank_adicCompletion`). PROVED. -/
theorem finrank_qp (p : Nat.Primes) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (vP p).asIdeal] :
    letI := qpAlg K p w
    Module.finrank ℚ_[p] (w.adicCompletion K) = w.asIdeal.ramificationIdx ℤ * w.asIdeal.inertiaDeg ℤ := by
  let _ := qpAlg K p w
  rw [Algebra.finrank_eq_of_equiv_equiv (qpEquiv p)
    (RingEquiv.refl (w.adicCompletion K)) rfl]
  have : Finite (𝓞 K ⧸ w.asIdeal) := inferInstance
  exact HeightOneSpectrum.finrank_adicCompletion (vP p) w
theorem vP_asIdeal (p : Nat.Primes) : (vP p).asIdeal = Ideal.span {((p : ℕ) : ℤ)} := by
  change (Ideal.span {((p : ℕ) : ℤ)}).map (Rat.IsIntegralClosure.intEquiv ℤ).symm = _
  rw [Ideal.map_span]
  simp

theorem ne_bot_of_mem_primesAbove {p : ℕ} (hp : p ≠ 0) {P : Ideal (𝓞 K)} (hP : P ∈ primesAbove K p) :
    P ≠ ⊥ := by
  rintro rfl
  have h := hP.2.over
  rw [Ideal.under_bot] at h
  have : ((p : ℤ)) ∈ (⊥ : Ideal ℤ) := h ▸ Ideal.mem_span_singleton_self _
  simp [hp] at this

/-- the height-one prime of `𝓞 K` given by a prime ideal above `p` -/
def placeOf {p : ℕ} (hp : p ≠ 0) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p) :
    HeightOneSpectrum (𝓞 K) := ⟨P, hP.1, ne_bot_of_mem_primesAbove K hp hP⟩

theorem placeOf_liesOver (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p) :
    (placeOf K p.2.ne_zero P hP).asIdeal.LiesOver (vP p).asIdeal := by
  rw [vP_asIdeal]; exact hP.2

/-- The data of the place `w` of `K` above `p`, built from its genuine completion `K_w`:
`d_w = [K_w : ℚ₂]` (or `0` for odd `p`) and `h^i(K_w, W)`, `W = 𝔽₂²` trivial. -/
def placeEntry (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p)
    (c : LocalCondition) (cd : ℕ) : PlaceData :=
  haveI := placeOf_liesOver K p P hP
  letI := qpAlg K p (placeOf K p.2.ne_zero P hP)
  { cond := c,
    deg := if (p : ℕ) = 2 then Module.finrank ℚ_[p] ((placeOf K p.2.ne_zero P hP).adicCompletion K)
      else 0,
    condDim := cd,
    localH0 := Module.finrank (ZMod 2) (continuousCohomology 0
      (trivialGaloisRep ((placeOf K p.2.ne_zero P hP).adicCompletion K) (Fin 2 → ZMod 2))),
    localH1 := Module.finrank (ZMod 2) (continuousCohomology 1
      (trivialGaloisRep ((placeOf K p.2.ne_zero P hP).adicCompletion K) (Fin 2 → ZMod 2))),
    localH2 := Module.finrank (ZMod 2) (continuousCohomology 2
      (trivialGaloisRep ((placeOf K p.2.ne_zero P hP).adicCompletion K) (Fin 2 → ZMod 2))) }

theorem placeEntry_deg (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p)
    (c : LocalCondition) (cd : ℕ) :
    (placeEntry K p P hP c cd).deg =
      if (p : ℕ) = 2 then P.ramificationIdx ℤ * P.inertiaDeg ℤ else 0 := by
  have := placeOf_liesOver K p P hP
  simp only [placeEntry]
  split_ifs
  · exact finrank_qp K p (placeOf K p.2.ne_zero P hP)
  · rfl

theorem qp_finiteDimensional (p : Nat.Primes) (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p) :
    letI := (placeOf_liesOver K p P hP)
    letI := qpAlg K p (placeOf K p.2.ne_zero P hP)
    FiniteDimensional ℚ_[p] ((placeOf K p.2.ne_zero P hP).adicCompletion K) := by
  have := placeOf_liesOver K p P hP
  let _ := qpAlg K p (placeOf K p.2.ne_zero P hP)
  have hP' : P.IsPrime := hP.1
  apply Module.finite_of_finrank_pos
  rw [finrank_qp K p (placeOf K p.2.ne_zero P hP)]
  exact one_le_ramificationIdx_mul_inertiaDeg P

theorem placeEntry_counts (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial) (p : Nat.Primes)
    (P : Ideal (𝓞 K)) (hP : P ∈ primesAbove K p) (c : LocalCondition) (cd : ℕ)
    (hc : (placeEntry K p P hP c cd).condDim =
      (placeEntry K p P hP c cd).cond.dim (placeEntry K p P hP c cd).deg) :
    (placeEntry K p P hP c cd).Counts := by
  have := placeOf_liesOver K p P hP
  let _ := qpAlg K p (placeOf K p.2.ne_zero P hP)
  have := qp_finiteDimensional K p P hP
  exact placeData_counts_of_prints h28 h23 p ((placeOf K p.2.ne_zero P hP).adicCompletion K) c cd hc

/-- The list of places of `K` above `p` (empty unless `p` is prime). -/
def placesList (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ) (p : ℕ) :
    List PlaceData :=
  if hp : p.Prime then
    ((primesAbove_finite (K := K) p).toFinset.attach.toList).map fun P =>
      placeEntry K ⟨p, hp⟩ P.1 ((primesAbove_finite (K := K) p).mem_toFinset.mp P.2)
        (cond P.1) (condDim P.1)
  else []

/-- **RC6's `places_length`**: one list entry per prime of `K` above `p` (at most two,
`QuadraticPlaces`). PROVED. -/
theorem length_placesList (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    {p : ℕ} (hp : p.Prime) : (placesList K cond condDim p).length = nPlaces K p := by
  simp only [placesList, hp, dite_true, List.length_map, Finset.length_toList, Finset.card_attach]
  rw [nPlaces, Set.ncard_eq_toFinset_card _ (primesAbove_finite p)]

theorem mem_placesList {cond : Ideal (𝓞 K) → LocalCondition} {condDim : Ideal (𝓞 K) → ℕ}
    {p : ℕ} (hp : p.Prime) {w : PlaceData} (hw : w ∈ placesList K cond condDim p) :
    ∃ P, ∃ hP : P ∈ primesAbove K p, w = placeEntry K ⟨p, hp⟩ P hP (cond P) (condDim P) := by
  simp only [placesList, hp, dite_true, List.mem_map, Finset.mem_toList, Finset.mem_attach,
    true_and] at hw
  obtain ⟨⟨P, hP⟩, rfl⟩ := hw
  exact ⟨P, _, rfl⟩

/-- **RC6's `places_deg`: `∑_{w ∣ p} d_w ≤ 2`** (tex 4576–4577), with `d_w = [K_w : ℚ₂]` for
`w ∣ 2` and `0` otherwise; for `p = 2` the sum is `∑ e f = [K : ℚ] = 2`. PROVED. -/
theorem deg_sum_placesList (hK : Module.finrank ℚ K = 2) (cond : Ideal (𝓞 K) → LocalCondition)
    (condDim : Ideal (𝓞 K) → ℕ) (p : ℕ) :
    ((placesList K cond condDim p).map PlaceData.deg).sum ≤ 2 := by
  by_cases hp : p.Prime
  · simp only [placesList, hp, dite_true, List.map_map]
    rw [Finset.sum_map_toList]
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl (fun x _ => placeEntry_deg K ⟨p, hp⟩ x.1 _ _ _)]
    by_cases h2 : p = 2
    · simp only [h2, ite_true]
      rw [Finset.sum_attach (primesAbove_finite (K := K) p).toFinset
        (fun P => P.ramificationIdx ℤ * P.inertiaDeg ℤ)]
      have : (Ideal.span {(p : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp hp)
      have := (primesAbove_finite (K := K) p).fintype
      rw [← sum_ramificationIdx_mul_inertiaDeg (K := K) (p := p) hK]
      rw [← Finset.sum_coe_sort]
      apply le_of_eq
      exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun P => Set.Finite.mem_toFinset _)
        _ _ (fun _ => rfl)
    · simp [h2]
  · simp [placesList, hp]

/-- **RC6's `places_counts`** (tex 4544–4573): every place satisfies `PlaceData.Counts`, from the
PRINT leaves Milne ADT I.2.3/I.2.8 (RC6's `placeData_counts_of_prints`) applied to the genuine
completion `K_w`, given Elliot's table value of the condition (`hcond`, ELLIOT, RC6's
`Counts.cond`). PROVED. -/
theorem counts_placesList (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ) {p : ℕ} (hp : p.Prime)
    (hcond : ∀ w ∈ placesList K cond condDim p, w.condDim = w.cond.dim w.deg) :
    ∀ w ∈ placesList K cond condDim p, w.Counts := by
  intro w hw
  obtain ⟨P, hP, rfl⟩ := mem_placesList K hp hw
  exact placeEntry_counts K h28 h23 ⟨p, hp⟩ P hP _ _ (hcond _ hw)

end ZInQ.Contrib.CloudB3RC53.RankCounts
