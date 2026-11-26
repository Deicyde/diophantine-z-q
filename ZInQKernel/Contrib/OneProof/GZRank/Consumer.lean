import ZInQKernel.Contrib.OneProof.SilvermanRankOne

/-!
# The pole proof's consumer, with a point of infinite order in place of rank one

`ZInQ.OneProof.frozenTarget` proves pole completeness (Theorem 5.2) by
`SilvermanRank.poleCompleteness_of_rankOne hRC hCT (SilvermanRank.rankOne_of_aec hRank)`, which
unfolds to `PoleRC.poleCompleteness_of_crm`, `PoleRC.crm_of_restrictedConverse_proved` and
`PoleRC.crm_of_restrictedConverse_M` (`Contrib/PoleRC/MordellWeilM.lean`). The last reads its
rank hypothesis `PoleRC.KolyvaginRankOne` once, as `PoleRC.exists_not_isOfFinAddOrder_of_rank`:
the descent `PoleRC.DescentGlueM` asks only for a point of infinite order on `E_ℓ`.

This file copies that chain with the weaker hypothesis `NonTorsionOfAnalyticRankOne` (analytic
rank one gives a point of infinite order) in place of `KolyvaginRankOne`. Every other input is the
original one: Mordell's theorem at `E_ℓ` (`PoleRC.mordellWeilM`), the complete 2-descent
(`PoleRC.descentGlueM`), Lemma 5.4 from the Cassels–Tate pairing
(`PoleS12.lemma54At_of_casselsTatePairing`) and the simultaneous construction
(`PoleS12.simultaneousConstruction`), all proved. The originals are unchanged, and the old route
factors through the new one (`nonTorsion_of_kolyvaginRankOne`).
-/

namespace ZInQ.Manuscript.PoleRC.NonTorsion

open WeierstrassCurve

/-- **Analytic rank one gives a point of infinite order**, for every elliptic curve over `ℚ`:
`ord_{s=1} L(E, s) = 1` (`AnalyticRankOne E`) implies that `E(ℚ)` has a point of infinite
order. This is all of `KolyvaginRankOne` that the pole proof reads. -/
def NonTorsionOfAnalyticRankOne : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → AnalyticRankOne E →
    ∃ P : E.toAffine.Point, ¬ IsOfFinAddOrder P

/-- **PROVED**: the rank-one statement implies the weaker one
(`exists_not_isOfFinAddOrder_of_rank`). -/
theorem nonTorsion_of_kolyvaginRankOne (h : KolyvaginRankOne) : NonTorsionOfAnalyticRankOne :=
  fun E hE hA => exists_not_isOfFinAddOrder_of_rank (h E hE hA)

/-- **PROVED**, a copy of `PoleRC.crm_of_restrictedConverse_M` with `NonTorsionOfAnalyticRankOne`
in place of `KolyvaginRankOne`: `CR_M` from Theorem 5.3, Lemma 5.4, a point of infinite order at
analytic rank one, Mordell's theorem at `E_ℓ` and the complete 2-descent. -/
theorem crm_of_restrictedConverse_M_nt (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hNT : NonTorsionOfAnalyticRankOne) (hMW : MordellWeilM) (hD : DescentGlueM) : CRM := by
  intro ℓ hℓ hsf h12 h8 β hβ
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hE := curve_isElliptic hℓ0
  have hP := h54 ℓ hℓ hsf h12 h8
  have hA := hRC ℓ hℓ hsf h12 hP
  exact hD ℓ hℓ hsf h12 (hMW ℓ hℓ hsf h12) (hNT _ hE hA) h8 (β, 1) hβ

/-- **PROVED**, a copy of `PoleRC.crm_of_restrictedConverse_proved`: Mordell's theorem at `E_ℓ`
(`mordellWeilM`) and the complete 2-descent (`descentGlueM`) are proved. -/
theorem crm_of_restrictedConverse_proved_nt (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hNT : NonTorsionOfAnalyticRankOne) : CRM :=
  crm_of_restrictedConverse_M_nt SelmerCorankOne hRC h54 hNT mordellWeilM descentGlueM

end ZInQ.Manuscript.PoleRC.NonTorsion

namespace ZInQ.Manuscript.PoleS12.GZRank

open ZInQ.Manuscript.PoleRC.NonTorsion (NonTorsionOfAnalyticRankOne
  crm_of_restrictedConverse_proved_nt)

/-- **PROVED**, a copy of `SilvermanRank.poleCompleteness_of_rankOne` with a point of infinite
order at analytic rank one in place of rank one: pole completeness (Theorem 5.2) from Theorem 5.3
over the genuine Selmer condition, the Cassels–Tate pairing on the curves `E_ℓ`, and
`NonTorsionOfAnalyticRankOne`. -/
theorem poleCompleteness_of_nonTorsion
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : CasselsTatePairingCurves)
    (hNT : NonTorsionOfAnalyticRankOne) : PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (crm_of_restrictedConverse_proved_nt SelmerTwoPower.SelmerCorankOne hRC
      (lemma54At_of_casselsTatePairing hCT) hNT)
    simultaneousConstruction

/-- **PROVED**: the live route factors through the new consumer, since the rank-one input gives a
point of infinite order (`nonTorsion_of_kolyvaginRankOne`). -/
theorem poleCompleteness_of_rankOne_via_nonTorsion
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : CasselsTatePairingCurves)
    (hRank : PoleRC.KolyvaginRankOne) : PoleCompleteness :=
  poleCompleteness_of_nonTorsion hRC hCT
    (PoleRC.NonTorsion.nonTorsion_of_kolyvaginRankOne hRank)

end ZInQ.Manuscript.PoleS12.GZRank

#print axioms ZInQ.Manuscript.PoleRC.NonTorsion.nonTorsion_of_kolyvaginRankOne
#print axioms ZInQ.Manuscript.PoleRC.NonTorsion.crm_of_restrictedConverse_M_nt
#print axioms ZInQ.Manuscript.PoleRC.NonTorsion.crm_of_restrictedConverse_proved_nt
#print axioms ZInQ.Manuscript.PoleS12.GZRank.poleCompleteness_of_nonTorsion
#print axioms ZInQ.Manuscript.PoleS12.GZRank.poleCompleteness_of_rankOne_via_nonTorsion
