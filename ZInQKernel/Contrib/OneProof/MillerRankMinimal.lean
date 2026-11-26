import ZInQKernel.Contrib.OneProof.RankModelInvariant
import ZInQKernel.Contrib.PoleRC.MordellWeilM

/-! The published rank conclusion on global minimal equations, transported
to the actual analytic-rank and Mordell–Weil predicates of the pole proof. -/

namespace ZInQ.Manuscript.RankModel

open WeierstrassCurve NumberField IsDedekindDomain PoleRC

/-- An integral rational Weierstrass equation minimal at every finite place.
The local clauses use the same completions as Mathlib's Euler product. -/
def IsGlobalMinimalQ (E : WeierstrassCurve ℚ) : Prop :=
  IsIntegral ℤ E ∧ ∀ p : HeightOneSpectrum (𝓞 ℚ),
    IsMinimal (p.adicCompletionIntegers ℚ) (E.baseChange (p.adicCompletion ℚ))

/-- The rank-one projection of Miller, *LMS J. Comput. Math.* 14 (2011),
Theorem 4.4, pp. 336–337, in the global minimal model convention of §1,
p. 327. The Heegner field and Sha finiteness are further conclusions of the
source; neither is a premise. No prime restriction from the valuation-bound
conclusion is used. -/
def MillerRankOneOnMinimalQ : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsGlobalMinimalQ E → AnalyticRankOne E →
    Module.rank ℤ E.toAffine.Point = 1

/-- Existence of a global minimal Weierstrass model over `ℚ`, expressed via
an admissible change of coordinates and the actual local minimality tests. -/
def GlobalMinimalModelsQ : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∃ U : VariableChange ℚ, IsGlobalMinimalQ (U • E)

/-- The manuscript's analytic rank-one assertion is invariant under a
rational change of coordinates, with the same analytic continuation. -/
theorem analyticRankOne_variableChange (E : WeierstrassCurve ℚ) (U : VariableChange ℚ)
    (hΔ : E.Δ ≠ 0) : AnalyticRankOne (U • E) ↔ AnalyticRankOne E := by
  unfold AnalyticRankOne
  simp only [LSeries_variableChange E U hΔ]

/-- Transport the printed rank conclusion to the exact rank input on the
live pole route. Model existence is kept explicit, not hidden in the proof. -/
theorem kolyvaginRankOne_of_miller_minimal (hM : MillerRankOneOnMinimalQ)
    (hGlobal : GlobalMinimalModelsQ) : PoleRC.KolyvaginRankOne := by
  intro E hE hA
  let := hE
  obtain ⟨U, hU⟩ := hGlobal E hE
  have hA' := (analyticRankOne_variableChange E U E.isUnit_Δ.ne_zero).mpr hA
  exact (rank_variableChange E U).symm.trans (hM (U • E) inferInstance hU hA')

/-- The pole proof uses rank only on the manuscript's family, not on every
elliptic curve over `ℚ`. -/
def RankOneOnPoleFamily : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → AnalyticRankOne (curve (ℓ : ℚ)) →
    Module.rank ℤ (curve (ℓ : ℚ)).toAffine.Point = 1

/-- For the family caller, minimality of the displayed equations suffices:
there is no need to assume existence of global minimal models for all curves. -/
theorem rankOneOnPoleFamily_of_miller (hM : MillerRankOneOnMinimalQ)
    (hMinimal : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → IsGlobalMinimalQ (curve (ℓ : ℚ))) :
    RankOneOnPoleFamily := by
  intro ℓ hp hsf hc hA
  have hq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  exact hM _ (curve_isElliptic hq) (hMinimal ℓ hp hsf hc) hA

/-- The actual `CR_M` calculation, with the rank input narrowed to exactly
the equations used in the construction. Neither the Selmer premise nor the
rational-point descent has been changed. -/
theorem crm_of_familyRank (P : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse P) (h54 : Lemma54At P) (hRank : RankOneOnPoleFamily) : CRM := by
  intro ℓ hℓ hsf h12 h8 β hβ
  have hA := hRC ℓ hℓ hsf h12 (h54 ℓ hℓ hsf h12 h8)
  have hr := hRank ℓ hℓ hsf h12 hA
  exact descentGlueM ℓ hℓ hsf h12 (mordellWeilM ℓ hℓ hsf h12)
    (exists_not_isOfFinAddOrder_of_rank hr) h8 (β, 1) hβ

end ZInQ.Manuscript.RankModel
