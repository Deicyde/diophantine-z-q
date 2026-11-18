import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.KummerTwo
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SelmerCount
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SqrtMem
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.SelmerOfSqrt
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsGenus

/-!
# RankCounts: RC6's field `kummer`, proved (tex 4482–4492)

`h1F2_eq`: for an imaginary quadratic field `K` and a finite set `S` of primes containing those
above `2`, `dim_{𝔽₂} H¹(G_{K,S}, 𝔽₂) = 1 + |S| + dim Cl(𝒪_{K,S})[2]` — Elliot's Kummer count
("the unit term has dimension `1 + |S_T|`", with the class-group term). It combines
`Hom_cont(G_{K,S}, 𝔽₂) ≅ K(S,2)` (`KummerTwo`, `SqrtMem`, `SelmerOfSqrt`) with the Selmer count
(`SelmerCount`: Tau Ceti's exact sequence `1 → 𝒪_S^×/2 → K(S,2) → Cl_S[2] → 1`, the `S`-unit rank,
`μ₂(K) = {±1}`).

`kummer_field` is RC6's field in the exact form of `residualRankCounts_genus` (`|S_T|` counted as
`Σ_{p ∈ T} #(primes above p)`, `ncard_primesAboveSet`), and `residualRankCounts_kummer` is RC6's
`ResidualRankCounts` with both `genus` and `kummer` proved. Kinds: PROVED.
-/

noncomputable section
open NumberField IsDedekindDomain
namespace ZInQ.Contrib.CloudB3RC53.RankCounts
open KummerS

variable (K : Type) [Field K] [NumberField K]

/-- **`h¹(G_{K,S}, 𝔽₂) = 1 + |S| + rk₂ Cl(𝒪_{K,S})`** for an imaginary quadratic field and a finite
set `S` of primes containing those above `2` (tex 4482–4492). PROVED. -/
theorem h1F2_eq (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    h1F2 K S = 1 + S.ncard + TauCeti.twoRank (ClassGroup (S.integer K)) := by
  have hc : Nat.card (continuousCohomology 1 (F2rep K S)) =
      2 ^ (1 + S.ncard + TauCeti.twoRank (ClassGroup (S.integer K))) := by
    rw [Nat.card_congr (h1triv (GaloisGroupS K S) (ZMod 2)).toEquiv]
    change Nat.card (GaloisGroupS K S →ₜ* Multiplicative (ZMod 2)) = _
    rw [card_hom_eq_card_selmer S sqrtMemOfSelmer_proof selmerOfSqrtMem_proof hS2,
      selmerCount_proof K hK2 hTC S hS]
  have : Finite (continuousCohomology 1 (F2rep K S)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have hH := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := continuousCohomology 1 (F2rep K S))
  rw [hc, Nat.card_zmod] at hH
  exact (Nat.pow_right_injective le_rfl hH).symm


omit [NumberField K] in
theorem natCast_mem_asIdeal_iff {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) :
    ((p : ℤ) : 𝓞 K) ∈ v.asIdeal ↔ v.asIdeal ∈ primesAbove K p := by
  constructor
  · intro h
    exact ⟨v.isPrime, (Ideal.liesOver_span_iff v.isPrime.ne_top
      (Nat.prime_iff_prime_int.mp hp)).mpr (by simpa using h)⟩
  · intro h
    have := h.2.over
    have hp' : (p : ℤ) ∈ Ideal.under ℤ v.asIdeal := by
      rw [← this]; exact Ideal.mem_span_singleton_self _
    simpa using hp'

/-- The primes of `K` above a rational prime `p`, as height-one primes, number `nPlaces K p`. -/
theorem ncard_primesAbove_heightOne {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | ((p : ℤ) : 𝓞 K) ∈ v.asIdeal}.ncard = nPlaces K p := by
  rw [nPlaces]
  refine Set.ncard_congr (fun v _ => v.asIdeal) (fun v hv => (natCast_mem_asIdeal_iff K hp v).mp hv)
    (fun v w _ _ h => HeightOneSpectrum.ext h) (fun P hP => ?_)
  have hne : P ≠ ⊥ := ne_bot_of_mem_primesAbove K hp.ne_zero hP
  exact ⟨⟨P, hP.1, hne⟩, (natCast_mem_asIdeal_iff K hp ⟨P, hP.1, hne⟩).mpr hP, rfl⟩

/-- `|S_T| = Σ_{p ∈ T} #(primes above p)` (tex 4516–4517). -/
theorem ncard_primesAboveSet (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    (primesAboveSet K T).ncard = ∑ p ∈ T, nPlaces K p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [primesAboveSet]
  | insert q T hq ih =>
    have hT' : ∀ p ∈ T, p.Prime := fun p hp => hT p (Finset.mem_insert_of_mem hp)
    have hqp : q.Prime := hT q (Finset.mem_insert_self q T)
    have hunion : primesAboveSet K (insert q T) =
        {v : HeightOneSpectrum (𝓞 K) | ((q : ℤ) : 𝓞 K) ∈ v.asIdeal} ∪ primesAboveSet K T := by
      ext v; simp [primesAboveSet]
    have hdisj : Disjoint {v : HeightOneSpectrum (𝓞 K) | ((q : ℤ) : 𝓞 K) ∈ v.asIdeal}
        (primesAboveSet K T) := by
      rw [Set.disjoint_left]
      rintro v hvq ⟨p, hp, hvp⟩
      have hpq : p ≠ q := fun h => hq (h ▸ hp)
      have := Genus.prime_eq_of_mem v.isPrime.ne_top (hT' p hp) hqp hvp hvq
      exact hpq this
    rw [hunion, Set.ncard_union_eq hdisj
      ((primesAboveSet_finite K {q} (by simpa using hqp.ne_zero)).subset (by
        intro v hv; exact ⟨q, by simp, hv⟩))
      (primesAboveSet_finite K T fun p hp => (hT' p hp).ne_zero),
      ncard_primesAbove_heightOne K hqp, ih hT', Finset.sum_insert hq]

open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional

open Classical in
theorem prime_of_mem_primeSetT {N r : ℕ} {D : Finset ℕ} (k : ℤ) (hr : r.Prime)
    (hD : ∀ p ∈ D, p.Prime) : ∀ p ∈ primeSetT N r D (ramifiedPrimes K k), p.Prime := by
  intro p hp
  simp only [primeSetT, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact prime_of_mem_chargedPrimes hr hD p hp
  · have := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | rfl
    · exact Nat.prime_of_mem_primeFactors h
    · exact Nat.prime_two

open Classical in
/-- **RC6's field `kummer`** in the exact form of `residualRankCounts_genus`: for the imaginary
quadratic field `K = ℚ(√k)` and `S_T` the primes above `T = primeSetT N r D Ram`,
`h¹(G_{K,S_T}, 𝔽₂) = (1 + |S_T|) + dim Cl(𝒪_{K,S_T})[2]` (tex 4482–4492). PROVED. -/
theorem kummer_field {k : ℤ} {α : 𝓞 K} (hα : IsQuadraticRadicand K k α) (hK : IsTotallyComplex K)
    {N r : ℕ} (hN : N ≠ 0) (hr : r.Prime) {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) :
    h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDimST K k N r D := by
  rw [h1F2_eq K hα.1 hK _ (primesAboveSet_finite K _ (ne_zero_of_mem_primeSetT K k hN hr hD))
    (fun v hv => two_mem_primesAboveSet K
      (Finset.mem_union_left _ (two_mem_chargedPrimes hN)) v hv),
    ncard_primesAboveSet K _ (prime_of_mem_primeSetT K k hr hD)]

open Classical in
/-- **RC6's `ResidualRankCounts` with `kummer` and `genus` proved** (tex 4453–4648, 4482–4517).
The remaining named inputs are the old-Kummer row of Elliot's table (through `hcond`), the
archimedean allowance `arch_le` (proved separately by `ArchLe`), the Selmer-cone model bounds `hG`,
`hL`, and `transfer`. -/
def residualRankCounts_kummer (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (archTot : ℕ) (arch_le : archTot ≤ 4)
    {S : Type} [CommRing S] [StrongRankCondition S] (Dsel : SelData S)
    [∀ n, Module.Free S (Dsel.G.X n)] [∀ n, Module.Finite S (Dsel.G.X n)]
    [∀ n, Module.Free S (Dsel.U.X n)] [∀ n, Module.Finite S (Dsel.U.X n)]
    [∀ n, Module.Free S (Dsel.L.X n)] [∀ n, Module.Finite S (Dsel.L.X n)]
    (s : Finset ℤ) (rankTot : ℕ)
    (hrank : rankTot = ∑ n ∈ s, Module.finrank S ((selCx Dsel).X n))
    (hG : ∑ n ∈ s, Module.finrank S (Dsel.G.X n) ≤
      hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2)
    (hL : ∑ n ∈ s, Module.finrank S (Dsel.U.X n) + ∑ n ∈ s, Module.finrank S (Dsel.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum + archTot)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  residualRankCounts_genus K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD
    (kummer_field K hα hK hN hr hD) cond condDim hcond archTot arch_le Dsel s rankTot hrank hG hL
    genericRank transfer

end ZInQ.Contrib.CloudB3RC53.RankCounts
