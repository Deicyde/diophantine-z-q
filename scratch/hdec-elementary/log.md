# hdec-elementary log

## Step 1 (read sources)
- Read: h-trust.md §§0-2 (36 steps A1-F4), wk-h.md (whole), rv-lit.md §4-5, prereq-survey.md,
  Lean: Hypotheses/Height.lean (SixContactEstimate, contactSupport, heightH6, heightD, heightE0),
  HeightMin.lean (SixContactMin), JHeight.lean (JHeightBound S; sixContactMin_of_jHeightBound proved).
- Facts: SixContactMin = ∀ u ∉ 𝒞, ratHeight u ≤ heightH6 D * M_{S_mul}(u)^24.
  JHeightBound S = ∀ u ∉ 𝒞, ratHeight (Jmap u) ≤ (40·10⁴·2²⁴+22) * heightX D * M_S(u)^24,
  Jmap u = −57600 F(u)²/G(u)⁶.
- wk-h §4.3: abstract signature (ArakelovSig) admits a fake model ⇒ the packaged hypothesis is a
  j-height bound in disguise. Must avoid that in this task.
