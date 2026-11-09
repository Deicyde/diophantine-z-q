# ap-lean log

- Merged origin/wip/nt-22p. No referee reports (rv-nt22p-*) exist yet at start.
- .lake copied from ~/dzq (same commit); `lake build ZInQKernel` OK (5 min).
- Plan: AP/LemmaP.lean (Hensel in ℤ_[ℓ]), AP/GoodSlopeAP.lean, AP/WeakApprox.lean (CRT targets with
  ℓ-power denominators + existing weak_approx_q), AP/PoleValuations.lean (copy with Lemma P(3)
  branch), AP/SlopeCompleteness.lean, AP/Completeness.lean (duplicated chain to FrozenTarget),
  Hypotheses/PrimeAP.lean, AP/PropAP.lean, Main.lean variant.
- Leaf 1 (LemmaP.lean): PoleAbsorbHyp, lemmaP_one, lemmaP_two (open set in ℚ_ℓ), lemmaP_two_ball,
  lemmaP_two_rat: proved. Hensel via `hensels_lemma` for Y² - F(u,v) at u³.
- Leaf 2 (GoodSlope.lean): OldBounds, GoodSlopeAP, GoodSlope.goodSlopeAP, contactQuot_eq_one: proved.
- Leaf 3: WeakApprox.lean (weak_approx_targets, CRT idempotents), PoleValuations.lean
  (padicValRat_traceTheta_of_clear, lemmaP_three, pole_input_valuations_AP),
  SlopeCompleteness.lean (slope_complete_AP), Completeness.lean (SlopeRepresentationAP,
  ..._AP chain, Assembly.assembly_AP): proved, build OK.
