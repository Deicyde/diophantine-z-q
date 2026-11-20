import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# The forward rank theorem as an explicit literature boundary

For an elliptic curve over `ℚ`, analytic rank at most one implies equality of
analytic and Mordell–Weil rank and finiteness of the Shafarevich–Tate group.
This is a consequence of the following established results, not a new axiom:

* Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over ℚ:
  wild 3-adic exercises*, JAMS 14 (2001), 843–939, Theorem A.
* Silverman, *The Arithmetic of Elliptic Curves*, second edition (2009),
  Theorem C.13.6, p. 442: a surjective `ℚ`-morphism `X₀(N) → E`, with `N`
  allowed to be the conductor of `E`.
* Kolyvagin, *On the Mordell–Weil group and the Shafarevich–Tate group of
  modular elliptic curves*, ICM Kyoto 1990, Vol. I (1991), Theorem 1, p. 430.
  Its bound is `ar(E) ≤ 1`, including both ranks zero and one.

The combined result is proved over ℚ in Robert L. Miller, *Proving the Birch
and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank
zero and one*, LMS J. Comput. Math. 14 (2011), 327–350,
[Theorem 4.4, pp. 336–337](https://doi.org/10.1112/S1461157011000180).
Miller's §1 fixes a global minimal Weierstrass equation as a presentation of
the curve and defines analytic rank using the central order of its Hasse–Weil
`L`-function. The rank and finiteness conclusions in Theorem 4.4 are about
the rational point group and the full `Sha`; extra hypotheses on a prime in
the theorem govern only the subsequent valuation bound. This is an AI-READ
comparison with the journal version.

The reductions use the existing rational point group, `E.LSeries`, and the
all-place `SelmerTwoPower.sha`. They neither change those definitions nor assert
the restricted converse. In particular, the old `IsModular` premise of `hK` is
not used: the universally quantified forward theorem already includes the
modularity step for every elliptic curve over `ℚ`.
-/

namespace ZInQ.Manuscript.ForwardRankLiterature

open SelmerTwoPower (sha)

/-- Analytic rank `r` for the same entire continuation and Euler-product
L-series as `ZInQ.Manuscript.AnalyticRankOne`. -/
def AnalyticRankAt (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧ analyticOrderAt F 1 = r

/-- The rank-one specialization preserves the existing analytic predicate. -/
theorem analyticRankAt_one_iff (E : WeierstrassCurve ℚ) :
    AnalyticRankAt E 1 ↔ AnalyticRankOne E := by
  simp only [AnalyticRankAt, AnalyticRankOne, Nat.cast_one]

/-- The rank and finiteness part of Miller, LMS J. Comput. Math. 14 (2011),
Theorem 4.4, p. 336. The printed conclusion is
`rank E(ℚ) = r_an(E)` and finiteness of `Sha(E/ℚ)` when `r_an(E) ≤ 1`.
It includes both analytic ranks zero and one. The Lean statement names the
central order `r` using an entire continuation of the Hasse–Weil L-series and
keeps the full all-place `Sha`. It uses neither the auxiliary Heegner point
nor the valuation bound in the print. -/
def ForwardRankAtMostOne : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, r ≤ 1 →
    AnalyticRankAt E r →
      Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- The existing `hK` is a consequence of the universally quantified forward
rank theorem. The literature input is retained as a parameter, not an axiom. -/
theorem kolyvaginThm1_of_forwardRankAtMostOne (h : ForwardRankAtMostOne) :
    PoleS12.KolyvaginThm1 := by
  intro E hE _ hA
  have hA' : AnalyticRankAt E 1 := (analyticRankAt_one_iff E).mpr hA
  simpa only [Nat.cast_one] using h E hE 1 le_rfl hA'

/-- Rank one and finite `Sha` are both retained, not just the rank projection. -/
theorem rankOne_and_finiteSha (h : ForwardRankAtMostOne)
    (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) (hA : AnalyticRankOne E) :
    Module.rank ℤ E.toAffine.Point = 1 ∧ Finite (sha E) := by
  have hA' : AnalyticRankAt E 1 := (analyticRankAt_one_iff E).mpr hA
  simpa only [Nat.cast_one] using h E hE 1 le_rfl hA'

/-- The rank-zero case is included by the same non-strict bound. -/
theorem rankZero_and_finiteSha (h : ForwardRankAtMostOne)
    (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) (hA : AnalyticRankAt E 0) :
    Module.rank ℤ E.toAffine.Point = 0 ∧ Finite (sha E) := by
  simpa only [Nat.cast_zero] using h E hE 0 (by decide) hA

end ZInQ.Manuscript.ForwardRankLiterature
