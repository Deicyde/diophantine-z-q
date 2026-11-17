import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCMatrix
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCLocal

/-!
# Theorem 5.2 from Theorem 5.3 with the descent's combinatorial inputs proved

`poleCompleteness_of_restrictedConverse_core` combines the two proved halves of the manuscript's descent from
Theorem 5.3 to Theorem 5.2 (`diophantine_zq.tex` lines 1019–1121):

* `Simul.matrixRealization` (the simultaneous matrix construction of lines 1033–1060, following the retained
  source S12, `parity-frozen-4eaee875.tex` lines 543–703);
* `dimThreeCount` (the dimension-three count of lines 1061–1074, from the local images at `ℝ`, `2`, `3`,
  `q ∣ ℓ` and the good primes, following S12 lines 317–453).

What remains as hypotheses is exactly what the manuscript cites at this point: Theorem 5.3 itself, Lemma 5.4
(here the interface `Lemma54At`, for the Selmer predicate `SelmerCorankOne`), Lemma 5.5's rank assertion
(`KolyvaginRankOne`: BCDT Theorem A with Kolyvagin Theorem 1) and Mordell's theorem (`MordellWeil`).
-/

namespace ZInQ.Manuscript.PoleRC

/-- **Theorem 5.2 from Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121), with the simultaneous construction
and the local images proved. -/
theorem poleCompleteness_of_restrictedConverse_core (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_localProved SelmerCorankOne hRC h54 hK hMW Simul.matrixRealization

end ZInQ.Manuscript.PoleRC
