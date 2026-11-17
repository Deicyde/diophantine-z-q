import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRC
import ZInQKernel.Contrib.PoleRC.LocalTwo
import ZInQKernel.Contrib.PoleRC.LocalGood

/-!
# Theorem 5.2 from Theorem 5.3 with the four local images proved

Lane R3-local (fork issue #83). The four local-image Props of `Count.lean` are theorems:
`localTwo` (`LocalTwo.lean`), `localThree` and `localBad` (`LocalThreeBad.lean`), `localGood`
(`LocalGood.lean`), following Elliot's local Selmer calculations in S12
(`parity-frozen-4eaee875.tex` lines 317–453); see each file for the map to S12's lines and the
labelled departures. Hence the manuscript's dimension-three count (`DimThreeCount`, lines
1061–1074) is proved, and `poleCompleteness_of_restrictedConverse_final` loses its four local
hypotheses.
-/

namespace ZInQ.Manuscript.PoleRC

/-- **The dimension-three count** (`diophantine_zq.tex` lines 1061–1074), proved. -/
theorem dimThreeCount : DimThreeCount :=
  dimThreeCount_of_local localTwo localThree localBad localGood

/-- **Theorem 5.2 from Theorem 5.3**, with the local images proved: what remains is Theorem 5.3,
Lemma 5.4 at `E_ℓ` (interface for the abstract Selmer predicate), the printed leaves of Lemma 5.5
(`KolyvaginRankOne`), Mordell's theorem, and the realization of the matrix conditions
(`MatrixRealization`, ELLIOT: S11–S12). -/
theorem poleCompleteness_of_restrictedConverse_localProved
    (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeil) (hR : MatrixRealization) :
    Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_final SelmerCorankOne hRC h54 hK hMW hR
    localTwo localThree localBad localGood

end ZInQ.Manuscript.PoleRC
