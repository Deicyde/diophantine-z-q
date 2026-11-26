import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.MillerRankMinimal
import ZInQKernel.Contrib.OneProof.GlobalMinimalModelsQ

/-!
# `hRank` and the rank-one slice of Miller's Theorem 4.4

The root argument `hRank` is the rank-one line of Silverman, *The Arithmetic of Elliptic
Curves*, 2nd ed., App. C, Evidence 16.5.5, for every Weierstrass curve over `ℚ`
(`PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne`).

`MillerRankOneOnMinimalQ` (in `MillerRankMinimal`) is the rank-one slice of the rank clause of
Miller, *LMS J. Comput. Math.* 14 (2011), Theorem 4.4, pp. 336–337, on global minimal
Weierstrass equations, the convention of the paper (§1, p. 327): analytic rank one implies
Mordell–Weil rank one. It does not mention the Shafarevich–Tate group.

The two statements are equivalent (`millerRankOneOnMinimalQ_iff`), so the rank-one slice is
not stronger than `hRank`. The passage from global minimal equations to arbitrary ones uses
`globalMinimalModelsQ` (every elliptic curve over `ℚ` has a global minimal equation) and the
invariance of the rank and of the Hasse–Weil `L`-series under a change of coordinates
(`rank_variableChange`, `LSeries_variableChange`).
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.RankModel

/-- `hRank` is equivalent to the rank-one slice of Miller's Theorem 4.4 on global minimal
equations. Kind: PROVED. -/
theorem millerRankOneOnMinimalQ_iff :
    MillerRankOneOnMinimalQ ↔ PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne := by
  constructor
  · intro h E hE F hF hL hz hd
    exact kolyvaginRankOne_of_miller_minimal h globalMinimalModelsQ E hE
      ((PoleS12.SilvermanRank.analyticRankOne_iff_value_deriv E).mpr ⟨F, hF, hL, hz, hd⟩)
  · intro h E hE _ hA
    obtain ⟨F, hF, hL, hz, hd⟩ :=
      (PoleS12.SilvermanRank.analyticRankOne_iff_value_deriv E).mp hA
    exact h E hE F hF hL hz hd

/-- **`hRank` from the rank-one slice of Miller's Theorem 4.4.** Kind: PROVED from the named
print `MillerRankOneOnMinimalQ`. -/
theorem silvermanAEC_C_16_5_5_RankOne_of_millerRankOne (h : MillerRankOneOnMinimalQ) :
    PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne :=
  millerRankOneOnMinimalQ_iff.mp h

end ZInQ.Manuscript.RankModel
