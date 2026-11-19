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

The named printed statements were read in their cited editions. This is
AI-READ source evidence, not a human reading or a kernel proof of those results.
`ForwardRankAtMostOne` remains an explicit input to each reduction below. It is
labelled a consequence of the three sources, not a literal transcription of
Kolyvagin's theorem with its modularity hypothesis removed.

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

/-- The classical forward rank theorem, obtained from BCDT Theorem A,
Silverman C.13.6 and Kolyvagin ICM Theorem 1 in the cited editions above.
This is an explicit literature consequence and is not proved by this definition.
Finiteness is for the genuine all-place `Sha(E/ℚ)`, not just its finite-level
2-torsion. No good-ordinary, non-CM, odd-prime or caller-supplied Heegner-point
hypothesis occurs in this consequence. -/
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
