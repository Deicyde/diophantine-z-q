import ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.CloudB3RC53.KummerCorankZero.Basic

/-!
# Miller's forward theorem in the restricted converse

The pole proof on its own needs only rank one, as supplied by Silverman.
Inside Theorem 5.3, the companion and calibration arguments use both low
ranks and the finiteness of the all-place Shafarevich–Tate group. The rank
and finiteness conclusions of Miller's Theorem 4.4 supply those inputs on
the analytic-rank definition already used by the restricted converse.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.ForwardRankLiterature

open ZInQ.Contrib.CloudB3RC53
open SelmerTwoPower

/-- The rank and finiteness conclusions of Robert L. Miller, *Proving the Birch
and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank
zero and one*, LMS J. Comput. Math. 14 (2011), pp. 336–337, Theorem 4.4
(doi:10.1112/S1461157011000180; journal version, AI-READ). For an elliptic
curve over ℚ of analytic rank `r ≤ 1`, the Mordell–Weil rank is `r` and
the full Shafarevich–Tate group is finite. Section 1 presents the curve in
global minimal Weierstrass form and uses the Hasse–Weil L-function.
The extra prime hypotheses in Theorem 4.4 concern the valuation bound only.
The Heegner field is a conclusion of the source, which this projection
does not need. -/
def ForwardRankAtMostOne : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, r ≤ 1 →
    AnalyticRank E r → Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- Fill the old forward-rank field of the Theorem 5.3 proof from Miller.
The old modularity premise does no work in this implication. -/
theorem kolyvaginThm1Printed_of_miller (hM : ForwardRankAtMostOne) :
    KolyvaginThm1Printed :=
  fun E hE _ r hr hA => hM E hE r hr hA

/-- The analytic-rank-zero step used by the companion argument. The Kummer
identification uses both the rank and finiteness conclusions. -/
theorem selmerCorankZero_of_miller (hM : ForwardRankAtMostOne)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (hA : AnalyticRank E 0) :
    Z2Corank (selmerTwoPower E) 0 := by
  obtain ⟨hr, hSha⟩ := hM E hE 0 (by decide) hA
  exact KummerCorankZero.kummerCorankZero_proof E hE (by simpa using hr) hSha

/-- The rank-one conclusion consumed by the pole descent. -/
theorem rankOne_of_miller (hM : ForwardRankAtMostOne) : PoleRC.KolyvaginRankOne := by
  intro E hE hA
  have hA' := (analyticRank_one_iff E).mpr hA
  simpa only [Nat.cast_one] using (hM E hE 1 le_rfl hA').1

/-- Miller also supplies the exact `hRank` type used by the headline, via
the analytic-order bridge already proved for Silverman's statement. -/
theorem silvermanRankOne_of_miller (hM : ForwardRankAtMostOne) :
    PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne := by
  intro E hE F hF hL hz hd
  exact rankOne_of_miller hM E hE
    ((PoleS12.SilvermanRank.analyticRankOne_iff_value_deriv E).mpr ⟨F, hF, hL, hz, hd⟩)

/-- In the sources used by Theorem 5.3, replace the old Kolyvagin input.
BCDT still supplies modularity for other parts of Theorem 5.3. -/
theorem prints_of_miller (hM : ForwardRankAtMostOne) (hB : PoleS12.BCDTThmA)
    (hD : DokchitserThm18) (hC : CST.CSTThm11Split) : Prints :=
  ⟨hB, kolyvaginThm1Printed_of_miller hM, hD, hC⟩

/-- Theorem 5.3 from the existing proof assembly with Miller supplying
the forward rank step. The `RCLeaves` inputs are unchanged. -/
theorem restrictedConverseGenuine_of_miller (hM : ForwardRankAtMostOne)
    (hB : PoleS12.BCDTThmA) (hD : DokchitserThm18) (hC : CST.CSTThm11Split)
    (hL : RC.Wiring.RCLeaves) : RestrictedConverseGenuine :=
  RC.Wiring.restrictedConverseGenuine_of_leaves (prints_of_miller hM hB hD hC) hL

/-- One forward-rank input suffices for Theorem 5.3 and for the subsequent
pole descent when those two assemblies are used together. -/
theorem poleCompleteness_of_miller_and_rcLeaves (hM : ForwardRankAtMostOne)
    (hB : PoleS12.BCDTThmA) (hD : DokchitserThm18) (hC : CST.CSTThm11Split)
    (hL : RC.Wiring.RCLeaves) (hCT : PoleS12.CasselsTatePairingCurves) :
    ZInQ.Manuscript.PoleCompleteness :=
  PoleS12.SilvermanRank.poleCompleteness_of_rankOne
    (restrictedConverseGenuine_of_miller hM hB hD hC hL) hCT (rankOne_of_miller hM)

end ZInQ.Manuscript.ForwardRankLiterature
