import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCounts
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LocalCounts
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.ResidualBridge

/-!
# RankCounts: RC6's `ResidualRankCounts` with the local data and the Selmer-cone model plugged in

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4453–4648.
`residualRankCounts_full` refines `residualRankCounts_of` (`ResidualCounts.lean`):

* the places are the genuine places of `K` above each charged prime (`LocalCounts.placesList`),
  so `places_length`, `places_deg` and `places_counts` are PROVED (the last from the PRINT leaves
  Milne ADT I.2.3/I.2.8 of RC6's `LocalPrints`, given Elliot's table value of each condition,
  `hcond`, ELLIOT);
* `cone` is PROVED by the Duality lane's `cone_of_selmerModel`
  (`SelmerDuality/ResidualBridge.lean`) from a finite free Selmer-cone model `selCx Dsel` of total
  rank `rankTot`, whose global part has total rank at most `globalTot = h⁰ + h¹ + h²` and whose
  local part has total rank at most the place costs plus `archTot` (inputs `hG`, `hL`).

Remaining named inputs (RC6 types, genuine values substituted): `kummer`, `genus` (with `clDim`
free here; both are proved downstream, `genus` with the genuine `clDim` in
`ResidualCountsGenus.lean` and `kummer` in `ResidualCountsKummer.lean`),
`hcond` (ELLIOT table), `arch_le` (PROVED for the genuine archimedean total:
`archLe_proof`, `archTotal_eq_four` in `ArchCounts.lean`), the cone-model rank bounds `hG`, `hL`, and `transfer` (assigned
to the MinimalComplexes lane). The bounded `genericRank` is free (constrained only by `transfer`);
it is not yet the genuine `N(E, A, j)`. Kinds: PROVED from the named inputs.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional

variable (K : Type) [Field K] [NumberField K]

theorem prime_of_mem_chargedPrimes {N r : ℕ} {D : Finset ℕ} (hr : r.Prime)
    (hD : ∀ p ∈ D, p.Prime) : ∀ p ∈ chargedPrimes N r D, p.Prime := by
  intro p hp
  simp only [chargedPrimes, Finset.mem_union, Finset.mem_singleton] at hp
  rcases hp with (hp | rfl) | hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact hr
  · exact hD p hp

open Classical in
/-- **RC6's `ResidualRankCounts` with the genuine places and the Selmer-cone model** (tex
4453–4648). PROVED from the PRINT leaves Milne ADT I.4.10, I.5.1 (global), I.2.3, I.2.8 (local)
and the named inputs listed in the module docstring. As in `residualRankCounts_of`, `genericRank`
is free (constrained only by `transfer`); it is not yet the genuine `N(E, A, j)`. -/
def residualRankCounts_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    -- the global inputs (genus route)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
    -- the local conditions and Elliot's table (ELLIOT)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (archTot : ℕ) (arch_le : archTot ≤ 4)
    -- the Selmer-cone model (Duality lane)
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
    -- the transfer (MinimalComplexes lane)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  residualRankCounts_of K h410 h51 k α hα hK N hN A hA r hr D hD clDim genus kummer
    (placesList K cond condDim)
    (fun p hp => length_placesList K cond condDim (prime_of_mem_chargedPrimes hr hD p hp))
    (fun p _ => deg_sum_placesList K hα.1 cond condDim p)
    (fun p hp => counts_placesList K h28 h23 cond condDim
      (prime_of_mem_chargedPrimes hr hD p hp) (hcond p hp))
    archTot arch_le rankTot
    (SelmerDuality.cone_of_selmerModel Dsel s N r D (placesList K cond condDim) _ archTot rankTot
      hrank hG hL)
    genericRank transfer

open Classical in
/-- **Lemma `ex:limits-residual-bound`, `N(E,A,j) ≤ 56 ω(2N) + 8A + 56j + 70`** (tex 4453–4648),
from `residualRankCounts_full`: the PRINT leaves, the genuine global and local counts, the
Selmer-cone model and the named inputs `kummer`, `genus`, `hcond`, `arch_le`, `hG`, `hL`,
`transfer`. PROVED. -/
theorem residualRankBound_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
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
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) :
    genericRank ≤ 56 * (2 * N).primeFactors.card + 8 * A + 56 * D.card + 70 :=
  (residualRankCounts_full K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD clDim genus kummer
    cond condDim hcond archTot arch_le Dsel s rankTot hrank hG hL genericRank transfer).genericRank_le

end ZInQ.Contrib.CloudB3RC53.RankCounts
