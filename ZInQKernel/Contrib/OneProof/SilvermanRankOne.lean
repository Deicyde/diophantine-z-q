import ZInQKernel.Contrib.OneProof.CasselsTatePairing

/-!
# Analytic rank one implies Mordell–Weil rank one: the pole proof's exact input

J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Springer GTM 106
(2009), Appendix C, Evidence 16.5.5, pp. 452–453, displays the implication
`L_E(1) = 0` and `L'_E(1) ≠ 0` imply `rank E(ℚ) = 1` for elliptic curves over
`ℚ`. The text after the display removes the historical modularity assumption.
This is the rank-one line only, not a finite-Shafarevich–Tate claim. Theorem
C.13.6, p. 442, is the modularity theorem, not the rank-one display.
-/

namespace ZInQ.Manuscript.PoleS12.SilvermanRank

/-- Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. (2009), Appendix C,
Evidence 16.5.5, p. 453, rank-one line. The Hasse–Weil L-function is represented
by its analytic continuation from the half-plane of absolute convergence.
Kind: PRINT. -/
def SilvermanAEC_C_16_5_5_RankOne : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ F : ℂ → ℂ,
    Differentiable ℂ F → (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) →
    F 1 = 0 → deriv F 1 ≠ 0 → Module.rank ℤ E.toAffine.Point = 1

/-- A simple central zero in the analytic-order convention is exactly the
value-and-derivative condition of the printed display. Kind: PROVED. -/
theorem analyticRankOne_iff_value_deriv (E : WeierstrassCurve ℚ) :
    AnalyticRankOne E ↔ ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧ F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  constructor
  · rintro ⟨F, hF, hL, ho⟩
    have ha := hF.analyticAt 1
    have hz : F 1 = 0 := by
      by_contra h
      have hzero := ha.analyticOrderAt_eq_zero.mpr h
      rw [ho] at hzero
      exact one_ne_zero hzero
    have hd : analyticOrderAt (deriv F) 1 = 0 := by
      exact_mod_cast analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using ho)
    exact ⟨F, hF, hL, hz, ha.deriv.analyticOrderAt_eq_zero.mp hd⟩
  · rintro ⟨F, hF, hL, hz, hd⟩
    exact ⟨F, hF, hL, (hF.analyticAt 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd⟩

/-- The exact rank-only forward input consumed by the pole argument, from the
rank-one line in Evidence 16.5.5. Kind: PROVED from the named print. -/
theorem rankOne_of_aec (h : SilvermanAEC_C_16_5_5_RankOne) : PoleRC.KolyvaginRankOne := by
  intro E hE hA
  obtain ⟨F, hF, hL, hz, hd⟩ := (analyticRankOne_iff_value_deriv E).mp hA
  exact h E hE F hF hL hz hd

/-- The same pole construction as the live proof, with its exact rank-only
input supplied directly. Theorem 5.3 and the Cassels–Tate pairing are unchanged.
Kind: PROVED from the named inputs. -/
theorem poleCompleteness_of_rankOne
    (hRC : SelmerTwoPower.RestrictedConverseGenuine) (hCT : CasselsTatePairingCurves)
    (hRank : PoleRC.KolyvaginRankOne) : PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (lemma54At_of_casselsTatePairing hCT) hRank)
    simultaneousConstruction

end ZInQ.Manuscript.PoleS12.SilvermanRank
