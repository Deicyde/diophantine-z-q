import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Inflation
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.QuadraticPlaces
import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualBound

/-!
# RankCounts: the constructor of RC6's `ResidualRankCounts`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4453–4648.

Lane RC6's structure `ZInQ.Manuscript.RC.Limits.ResidualRankCounts`
(`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`) records the counts behind (5.1) as
numbers; `ResidualRankCounts.genericRank_le` turns them into
`N(E,A,j) ≤ 56 ω(2N) + 8A + 56j + 70`. `residualRankCounts_of` builds an instance for an imaginary
quadratic field `K = ℚ(√k)` in which:

* `Ram` is the genuine set of ramified primes (`ramifiedPrimes K k`) and `ram_sub` is PROVED
  (`QuadraticPlaces`);
* `globalTot = h⁰ + h¹ + h²` with `hⁱ = dim_{𝔽₂} H^i(G_{K,S₀}, W)`, `W = 𝔽₂²` trivial, for the genuine
  `G_{K,S₀}` (`GlobalPrints`), and `global_le` is PROVED through RC6's genus-route structure
  `GlobalCountsGenus` (`globalCountsGenus_of`), whose fields `nPlaces_le_two`, `nPlaces_ram`,
  `h0_eq`, `h1_eq` and `inflation` are PROVED (the last from `Inflation.lean`, with the finiteness of
  `H¹(G_{K,S_T}, 𝔽₂)` from Milne ADT I.5.1), and `euler` follows from the PRINT leaves Milne ADT
  I.4.10/I.5.1;
* `places_length` is PROVED from `nPlaces ≤ 2` when the place list over `p` has one entry per
  prime of `K` above `p`.

The remaining named inputs, with RC6's types (the genuine values substituted where they exist):
* `kummer` (tex 4482–4492; GLUE: Kummer theory and the `S`-unit theorem for `G_{K,S_T}`) and `genus`
  (tex 4494–4517; ELLIOT's genus argument), as in `GlobalCountsGenus`, with
  `h1ST = dim H¹(G_{K,S_T}, 𝔽₂)` and `nPlaces = #(primes above p)`; `clDim` is the dimension of
  `Cl(𝒪_{K,S_T})[2]`, not defined here (both are proved downstream: `genus` in
  `ResidualCountsGenus.lean`, `kummer` in `ResidualCountsKummer.lean`);
* `places_deg`, `places_counts` (tex 4544–4582; local degrees and the local table; RC6's
  `placeData_counts_of_prints` gives the local-cohomology part from Milne ADT I.2.3, I.2.8);
* `arch_le` (tex 4584–4591);
* `cone` (tex 4593–4597; the Selmer-cone model, see the Duality lane's `cone_of_selmerModel` in
  `SelmerDuality/ResidualBridge.lean`, plugged in by `ResidualCountsFull.lean`);
* `transfer` (tex 4598–4647; Nekovář 7.8.8(ii) and RC6's `ResidualAlgebra`; the MinimalComplexes
  lane's route is in `ResidualTransfer/`).

`genericRank` is a free natural number bounded through `transfer`; it is not yet tied to the
genuine `N(E, A, j)`.

Kinds: PROVED from the named inputs.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits

variable (K : Type) [Field K] [NumberField K]

/-- The primes of `K` above a finite set `P` of rational numbers (`S₀ = primes above
chargedPrimes`, `S_T = primes above T`, tex 4468–4470). -/
def primesAboveSet (P : Finset ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ∃ p ∈ P, ((p : ℤ) : 𝓞 K) ∈ v.asIdeal}

theorem primesAboveSet_finite (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0) :
    (primesAboveSet K P).Finite := by
  have : primesAboveSet K P = ⋃ p ∈ P, {v : HeightOneSpectrum (𝓞 K) | ((p : ℤ) : 𝓞 K) ∈ v.asIdeal} := by
    ext v; simp [primesAboveSet]
  rw [this]
  refine Set.Finite.biUnion P.finite_toSet fun p hp => ?_
  have h : Ideal.span {((p : ℤ) : 𝓞 K)} ≠ 0 := by
    simpa using hP p hp
  refine (Ideal.finite_factors h).subset ?_
  intro v hv
  simpa [Ideal.span_singleton_le_iff_mem] using hv

omit [NumberField K] in
theorem primesAboveSet_mono {P Q : Finset ℕ} (h : P ⊆ Q) :
    primesAboveSet K P ⊆ primesAboveSet K Q := fun _ ⟨p, hp, hv⟩ => ⟨p, h hp, hv⟩

omit [NumberField K] in
theorem two_mem_primesAboveSet {P : Finset ℕ} (h2 : 2 ∈ P) (v : HeightOneSpectrum (𝓞 K))
    (hv : (2 : 𝓞 K) ∈ v.asIdeal) : v ∈ primesAboveSet K P := ⟨2, h2, by simpa using hv⟩

/-- `W = 𝔽₂²` with trivial action, as a representation of `G_{K,S}`. -/
abbrev Wrep (S : Set (HeightOneSpectrum (𝓞 K))) := trivialRepS (GaloisGroupS K S) (ZMod 2 × ZMod 2)

/-- `𝔽₂` with trivial action. -/
abbrev F2rep (S : Set (HeightOneSpectrum (𝓞 K))) := trivialRepS (GaloisGroupS K S) (ZMod 2)

/-- `dim_{𝔽₂} H^i(G_{K,S}, W)`. -/
abbrev hW (S : Set (HeightOneSpectrum (𝓞 K))) (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (continuousCohomology i (Wrep K S))

/-- `dim_{𝔽₂} H¹(G_{K,S}, 𝔽₂)`. -/
abbrev h1F2 (S : Set (HeightOneSpectrum (𝓞 K))) : ℕ :=
  Module.finrank (ZMod 2) (continuousCohomology 1 (F2rep K S))

theorem finrank_zmod2_sq : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by
  rw [Module.finrank_prod, Module.finrank_self]

/-- **RC6's genus-route global counts from the genuine `G_{K,S}`** (tex 4478–4533). PROVED from
the PRINT leaves Milne ADT I.4.10/I.5.1 and the inputs `kummer`, `genus`, `inflation` (the last is PROVED
in `residualRankCounts_of` by `rc6InflationOfPrint_proof`). Here
`S₀ ⊆ S_T` are finite sets of primes of the imaginary quadratic field `K = ℚ(√k)`, `S₀` containing
the primes above `2`, `T` a finite set of rational primes containing the ramified ones. -/
def globalCountsGenus_of (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (T Ram : Finset ℕ) (hRamT : Ram ⊆ T)
    (hRam : ∀ p ∈ Ram, IsRamifiedPrime K p) (S₀ ST : Set (HeightOneSpectrum (𝓞 K)))
    (hS₀ : S₀.Finite) (hS₀2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (clDim : ℕ) (genus : clDim + 1 ≤ Ram.card)
    (kummer : h1F2 K ST = (1 + ∑ p ∈ T, nPlaces K p) + clDim)
    (inflation : h1F2 K S₀ ≤ h1F2 K ST) : GlobalCountsGenus T Ram where
  ram_sub_T := hRamT
  nPlaces := nPlaces K
  nPlaces_le_two := fun p _ => nPlaces_le_two_of_finrank hα.1 p
  nPlaces_ram := fun p hp => nPlaces_eq_one_of_isRamifiedPrime hα.1 (hRam p hp)
  clDim := clDim
  genus := genus
  h1ST := h1F2 K ST
  kummer := kummer
  h1S0F2 := h1F2 K S₀
  inflation := inflation
  h0 := hW K S₀ 0
  h1 := hW K S₀ 1
  h2 := hW K S₀ 2
  h0_eq := by
    have := globalCountsImagQuad_proof h410 h51 K hα.1 hK S₀ hS₀ hS₀2 (ZMod 2 × ZMod 2)
      inferInstance inferInstance finrank_zmod2_sq
    exact this.1
  h1_eq := h1_eq_two_mul (G := GaloisGroupS K S₀)
  euler := by
    have := globalCountsImagQuad_proof h410 h51 K hα.1 hK S₀ hS₀ hS₀2 (ZMod 2 × ZMod 2)
      inferInstance inferInstance finrank_zmod2_sq
    exact this.2.1

theorem ne_zero_of_mem_chargedPrimes {N r : ℕ} {D : Finset ℕ} (_hN : N ≠ 0) (hr : r.Prime)
    (hD : ∀ p ∈ D, p.Prime) : ∀ p ∈ chargedPrimes N r D, p ≠ 0 := by
  intro p hp
  simp only [chargedPrimes, Finset.mem_union, Finset.mem_singleton] at hp
  rcases hp with (hp | rfl) | hp
  · exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  · exact hr.ne_zero
  · exact (hD p hp).ne_zero

open Classical in
theorem ne_zero_of_mem_primeSetT {N r : ℕ} {D : Finset ℕ} (k : ℤ) (hN : N ≠ 0) (hr : r.Prime)
    (hD : ∀ p ∈ D, p.Prime) : ∀ p ∈ primeSetT N r D (ramifiedPrimes K k), p ≠ 0 := by
  intro p hp
  simp only [primeSetT, Finset.mem_union] at hp
  rcases hp with hp | hp
  · exact ne_zero_of_mem_chargedPrimes hN hr hD p hp
  · have := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | rfl
    · exact (Nat.prime_of_mem_primeFactors h).ne_zero
    · decide

theorem two_mem_chargedPrimes {N r : ℕ} {D : Finset ℕ} (hN : N ≠ 0) :
    2 ∈ chargedPrimes N r D := by
  simp only [chargedPrimes, Finset.mem_union, Finset.mem_singleton]
  left; left
  exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_mul_right 2 N, by omega⟩

open Classical in
/-- **The constructor of RC6's `ResidualRankCounts`** (tex 4453–4648). PROVED from the PRINT leaves
Milne ADT I.4.10/I.5.1 and the named inputs listed in the module docstring, for an imaginary
quadratic field `K = ℚ(√k)` with `ω(k) ≤ A`, conductor `N`, moving prime `r`, derivative primes `D`,
`S₀ = primes above chargedPrimes N r D`, `S_T = primes above primeSetT N r D Ram`. The bounded
quantity `genericRank` is free (constrained only by `transfer`); it is not yet the genuine
`N(E, A, j)`. -/
def residualRankCounts_of (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    -- the global inputs (genus route)
    (clDim : ℕ) (genus : clDim + 1 ≤ (ramifiedPrimes K k).card)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim)
    -- the local inputs
    (places : ℕ → List PlaceData)
    (hlen : ∀ p ∈ chargedPrimes N r D, (places p).length = nPlaces K p)
    (places_deg : ∀ p ∈ chargedPrimes N r D, ((places p).map PlaceData.deg).sum ≤ 2)
    (places_counts : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ places p, w.Counts)
    (archTot : ℕ) (arch_le : archTot ≤ 4)
    -- the cone and the transfer
    (rankTot : ℕ)
    (cone : rankTot ≤ (hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2) +
      ∑ p ∈ chargedPrimes N r D, ((places p).map PlaceData.cost).sum + archTot)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  let S₀ := primesAboveSet K (chargedPrimes N r D)
  let G := globalCountsGenus_of K h410 h51 k α hα hK (primeSetT N r D (ramifiedPrimes K k))
    (ramifiedPrimes K k) Finset.subset_union_right
    (fun _ hp => (Finset.mem_filter.mp hp).2) S₀
    (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k)))
    (primesAboveSet_finite K _ (ne_zero_of_mem_chargedPrimes hN hr hD))
    (fun v hv => two_mem_primesAboveSet K (two_mem_chargedPrimes hN) v hv)
    clDim genus kummer
    (rc6InflationOfPrint_proof h51 K hK _ _
      (primesAboveSet_mono K Finset.subset_union_left)
      (primesAboveSet_finite K _ (ne_zero_of_mem_primeSetT K k hN hr hD))
      (fun v hv => primesAboveSet_mono K Finset.subset_union_left
        (two_mem_primesAboveSet K (two_mem_chargedPrimes hN) v hv)))
  { N := N
    N_ne_zero := hN
    k := k
    A := A
    omega_k_le := hA
    r := r
    D := D
    Ram := ramifiedPrimes K k
    ram_sub := Finset.filter_subset _ _
    globalTot := hW K S₀ 0 + hW K S₀ 1 + hW K S₀ 2
    global_le := G.total_le
    places := places
    places_length := fun p hp => (hlen p hp).trans_le (nPlaces_le_two_of_finrank hα.1 p)
    places_deg := places_deg
    places_counts := places_counts
    archTot := archTot
    arch_le := arch_le
    rankTot := rankTot
    cone := cone
    genericRank := genericRank
    transfer := transfer }

open Classical in
/-- **Lemma `ex:limits-residual-bound`, `N(E,A,j) ≤ 56 ω(2N) + 8A + 56j + 70`** (tex 4453–4648),
PROVED from the PRINT leaves Milne ADT I.4.10/I.5.1 and the named inputs of
`residualRankCounts_of` (kummer, genus, the local inputs, cone, transfer), through RC6's
`ResidualRankCounts.genericRank_le`. The bound is for a free `genericRank ≤ rankTot`; it is not
yet the genuine `N(E, A, j)`. -/
def ResidualRankBoundNode : Prop :=
  MilneADT_I_4_10_totallyComplex → MilneADT_I_5_1_totallyComplex →
  ∀ (K : Type) [Field K] [NumberField K] (k : ℤ) (α : 𝓞 K), IsQuadraticRadicand K k α →
    IsTotallyComplex K → ∀ (N : ℕ), N ≠ 0 → ∀ (A : ℕ), k.natAbs.primeFactors.card ≤ A →
    ∀ (r : ℕ), r.Prime → ∀ (D : Finset ℕ), (∀ p ∈ D, p.Prime) →
    ∀ (clDim : ℕ), clDim + 1 ≤ (ramifiedPrimes K k).card →
    h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDim →
    ∀ (places : ℕ → List PlaceData),
    (∀ p ∈ chargedPrimes N r D, (places p).length = nPlaces K p) →
    (∀ p ∈ chargedPrimes N r D, ((places p).map PlaceData.deg).sum ≤ 2) →
    (∀ p ∈ chargedPrimes N r D, ∀ w ∈ places p, w.Counts) →
    ∀ (archTot : ℕ), archTot ≤ 4 → ∀ (rankTot : ℕ),
    rankTot ≤ (hW K (primesAboveSet K (chargedPrimes N r D)) 0 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 1 +
        hW K (primesAboveSet K (chargedPrimes N r D)) 2) +
      ∑ p ∈ chargedPrimes N r D, ((places p).map PlaceData.cost).sum + archTot →
    ∀ (genericRank : ℕ), genericRank ≤ rankTot →
    genericRank ≤ 56 * (2 * N).primeFactors.card + 8 * A + 56 * D.card + 70

theorem residualRankBoundNode_proof : ResidualRankBoundNode := by
  intro h410 h51 K _ _ k α hα hK N hN A hA r hr D hD clDim genus kummer places hlen
    hdeg hcounts archTot harch rankTot hcone genericRank htransfer
  exact (residualRankCounts_of K h410 h51 k α hα hK N hN A hA r hr D hD clDim genus kummer
    places hlen hdeg hcounts archTot harch rankTot hcone genericRank htransfer).genericRank_le

end ZInQ.Contrib.CloudB3RC53.RankCounts
