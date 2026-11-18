import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ResidualCountsGenus
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.ArchCounts
import ZInQKernel.Contrib.OneProof.RC.Uniform.UniformLowerBound

/-!
# Theorem 5.3, Lane RC0 round 3: where (5.1) enters the uniform lower bound

Lemma `ex:limits-residual-bound` ((5.1), tex 4453–4648) bounds the reduced generic residual rank of
each ring instance with `ω(k) ≤ A` and `j` derivative labels by
`N(E, A, j) ≤ 56 ω(2N) + 8A + 56j + 70`, uniformly in the instance; "the same estimate bounds the
scalar `𝒪`-minimal models used below" (tex 4645–4648). In the proof of
Proposition `ex:limits-uniform-lower-bound` it is used once, in the outer argument: "write their
minimal completed models as `[𝒪_jⁿ --D_j--> 𝒪_jⁿ]`, fixing the bounded `n` on an outer-large set"
(tex 4935–4938), and again "For each fixed number of them (5.1) bounds the models" (tex 4953–4955).
It does not enter the height-one regularity (one ring instance at a time, "This requires no uniform
outer valuation bound", tex 5199–5200) nor (4.6).

In Lean the fixed size is part of the data of the outer configurations (batch 3's `OuterStage.n`,
lane RC0's `GenuineOuterStage.n`), so no conversion consumes (5.1); RC16's
`exists_eventually_size_eq` (the step "fixing the bounded `n` on an outer-large set") is not used by
`exLimitsUniformLowerBound`. This file records the step from (5.1) to that fixed size:

* `residualRankCounts_genusArch` (PROVED): batch 3's `residualRankCounts_genus` (the genus bound
  (5.1b) proved, `clDim` the genuine `2`-rank of the `S_T`-class group) with the archimedean
  allowance discharged by batch 3's `archLe_proof` (`archTot = archTotal K w` at the complex
  place). Remaining inputs: `kummer` (GLUE, Kummer theory and the `S`-unit theorem), `hcond`
  (ELLIOT table), the Selmer-cone rank bounds `hG`, `hL`, and `transfer` (RC6's transfer of the
  generic rank across the support change, tex 4612–4631; kept as an explicit input).
* `exists_eventually_size_eq_of_residual` (PROVED): if the inner minimal models of a sequence of
  instances have sizes at most their generic residual ranks (tex 4645–4648; GLUE, owner RC6 /
  batch 3 ResidualTransfer `minimalModelsExist_proof`) and the instances share `N`, `A` and the
  number `j = |D|` of derivative labels, then one size `n ≤ N(E, A, j)` occurs on an outer-large set
  (RC6's `ResidualRankCounts.genericRank_le` and RC16's `exists_eventually_size_eq`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53
  ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.PairedFunctional

open Classical in
/-- **RC6's `ResidualRankCounts` with the genus bound and the archimedean allowance proved** (tex
4453–4648, 4494–4517, 4584–4591): batch 3's `residualRankCounts_genus` at `archTot = archTotal K w`
for a complex place `w` of `K`, with `arch_le` discharged by batch 3's `archLe_proof`. Remaining
inputs: `kummer`, `hcond`, `hG`, `hL`, `transfer` (and the PRINT leaves Milne ADT I.4.10, I.5.1,
I.2.8, I.2.3). Kind: PROVED from the inputs. -/
def residualRankCounts_genusArch (K : Type) [Field K] [NumberField K]
    (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8) (h23 : MilneADT_I_2_3_trivial)
    (k : ℤ) (α : 𝓞 K) (hα : IsQuadraticRadicand K k α)
    (hK : IsTotallyComplex K) (N : ℕ) (hN : N ≠ 0) (A : ℕ) (hA : k.natAbs.primeFactors.card ≤ A)
    (r : ℕ) (hr : r.Prime) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime)
    (kummer : h1F2 K (primesAboveSet K (primeSetT N r D (ramifiedPrimes K k))) =
      (1 + ∑ p ∈ primeSetT N r D (ramifiedPrimes K k), nPlaces K p) + clDimST K k N r D)
    (cond : Ideal (𝓞 K) → LocalCondition) (condDim : Ideal (𝓞 K) → ℕ)
    (hcond : ∀ p ∈ chargedPrimes N r D, ∀ w ∈ placesList K cond condDim p,
      w.condDim = w.cond.dim w.deg)
    (w : InfinitePlace K) (hw : w.IsComplex)
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
      ∑ p ∈ chargedPrimes N r D, ((placesList K cond condDim p).map PlaceData.cost).sum +
        archTotal K w)
    (genericRank : ℕ) (transfer : genericRank ≤ rankTot) : ResidualRankCounts :=
  residualRankCounts_genus K h410 h51 h28 h23 k α hα hK N hN A hA r hr D hD kummer
    cond condDim hcond (archTotal K w) (archLe_proof K w hw) Dsel s rankTot hrank hG hL
    genericRank transfer

/-- **(5.1) fixes the inner size on an outer-large set** (tex 4935–4938, 4953–4955, 4645–4648):
for a sequence of instances with residual counts `R j` (e.g. `residualRankCounts_genusArch`) sharing
`N`, `A` and `j = |D|`, and inner minimal models of sizes `size j ≤ (R j).genericRank` (the
`𝒪`-minimal ranks are the reduced dimensions, tex 4645–4648), one size `n ≤ N(E, A, j)` occurs on
an outer-large set. Kind: PROVED (RC6's `genericRank_le`, RC16's `exists_eventually_size_eq`). -/
theorem exists_eventually_size_eq_of_residual {ι : Type*} (𝒰 : Ultrafilter ι)
    (R : ι → ResidualRankCounts) (N A d : ℕ) (hN : ∀ j, (R j).N = N) (hA : ∀ j, (R j).A = A)
    (hd : ∀ j, (R j).D.card = d) (size : ι → ℕ) (hsize : ∀ j, size j ≤ (R j).genericRank) :
    ∃ n ≤ residualBoundConstant (2 * N).primeFactors.card A d,
      ∀ᶠ j in (𝒰 : Filter ι), size j = n :=
  ZInQ.Manuscript.RC.Uniform.exists_eventually_size_eq 𝒰 size _ fun j => (hsize j).trans (by
    have h := (R j).genericRank_le
    rw [hN j, hA j, hd j] at h
    exact h)

end ZInQ.Manuscript.RC.Wiring
