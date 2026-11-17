import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Rank
import ZInQKernel.Contrib.OneProof.RC.Limits.ResidualBound

/-!
# Selmer duality, part 5: bridge to the residual-rank counts of (5.1)

Lemma `ex:limits-residual-bound` (`diophantine_zq.tex`, tex L4593–4597): "the total rank of the
Selmer cone (4.3) ... Cone shifts do not change this sum ... Further cancellation can only
decrease it". Lane RC6 records this as the field

```
cone : rankTot ≤ globalTot + ∑ p ∈ chargedPrimes N r D, ((places p).map PlaceData.cost).sum + archTot
```

of `ZInQ.Manuscript.RC.Limits.ResidualRankCounts`. This file proves that field, in its exact type,
for the finite free model `C^n = G^n ⊕ U^n ⊕ L^{n−1}` (`selCx`, `PairedFunctional/SelmerPairing`)
of the Selmer cone built from finite free models of the global complex `G`, the local conditions `U`
and the full local complexes `L` (`cone_of_selmerModel`): its total rank is the sum of the three
total ranks (`selCx_totalRank`), so it is at most `globalTot` plus the local and archimedean costs
as soon as `G` has total rank at most `globalTot` and `U ⊕ L` total rank at most the sum of the
place costs plus the archimedean allowance.

**Classification.** GLUE, PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.SelmerDuality

open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Manuscript.RC.Limits

universe u

/-- **RC6 field `cone`, from the Selmer cone model** (tex L4593–4597). Let `D` be Selmer data
`G --res--> L <--ι-- U` over a commutative ring `S` (with the strong rank condition) whose terms
are finite free, and `s` a finite set of degrees. If `rankTot` is the total rank of the Selmer cone
model `selCx D` over `s`, the global model has total rank at most `globalTot`, and the local
condition and full local models together have total rank at most the place costs plus `archTot`,
then RC6's field `cone` holds. -/
theorem cone_of_selmerModel {S : Type u} [CommRing S] [StrongRankCondition S] (D : SelData S)
    [∀ n, Module.Free S (D.G.X n)] [∀ n, Module.Finite S (D.G.X n)]
    [∀ n, Module.Free S (D.U.X n)] [∀ n, Module.Finite S (D.U.X n)]
    [∀ n, Module.Free S (D.L.X n)] [∀ n, Module.Finite S (D.L.X n)]
    (s : Finset ℤ) (N r : ℕ) (Dp : Finset ℕ) (places : ℕ → List PlaceData)
    (globalTot archTot rankTot : ℕ)
    (hrank : rankTot = ∑ n ∈ s, Module.finrank S ((selCx D).X n))
    (hG : ∑ n ∈ s, Module.finrank S (D.G.X n) ≤ globalTot)
    (hL : ∑ n ∈ s, Module.finrank S (D.U.X n) + ∑ n ∈ s, Module.finrank S (D.L.X (n - 1)) ≤
      ∑ p ∈ chargedPrimes N r Dp, ((places p).map PlaceData.cost).sum + archTot) :
    rankTot ≤ globalTot + ∑ p ∈ chargedPrimes N r Dp, ((places p).map PlaceData.cost).sum +
      archTot := by
  rw [hrank, selCx_totalRank]
  omega

end ZInQ.Contrib.CloudB3RC53.SelmerDuality
