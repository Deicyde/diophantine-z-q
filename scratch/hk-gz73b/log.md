# Gross–Zagier p. 310 reduction results

- **VERIFIED (base).** At `34f9cd14a`, the headline takes the height bundles and
  `hRC : RestrictedConverseGenuine`, `hCT : CasselsTatePairingCurves`,
  `hB : BCDTThmAPrinted`, and `hK : KolyvaginThm1`. The prior reduction
  in `ZInQKernel/Contrib/OneProof/HKGZ73/Reduction.lean` proves the matching
  newform's least-level property and two analytic-rank dictionaries. Its
  application required `PoleNewformLevelIsConductor`.
- **VERIFIED (target).** `HKRefereed.HKConsumed` is
  `∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (PoleRC.SelM ℓ).ncard = 8 →
  PoleS12.IsModular (curve (ℓ : ℚ)) → AnalyticRankOne (curve (ℓ : ℚ)) →
  ∃ P : (curve (ℓ : ℚ)).toAffine.Point, ¬ IsOfFinAddOrder P`.
  `hkConsumed_of_hK` uses the rank projection.
  `poleCompleteness_of_hkConsumed` feeds the point and the eight-class
  count to `PoleRC.descentGlueM`. See `docs/research/hk-refereed.md` and
  TeX L1005–1011, L1033–1069, L1072–1084, L1086–1097, L1111–1121.
- **VERIFIED (modularity interfaces).** `BCDTPrint.BCDTThmAPrinted` supplies
  `∃ (N : ℕ) (_ : NeZero N), Condition2At E N`, using the Introduction's
  eigenform condition. `bcdtThmA_of_printed` gives `PoleS12.BCDTThmA`, which
  for every elliptic `E/ℚ` produces `PoleS12.IsModular E`: a weight-two
  `Γ₀(N)` cusp form at some positive level with the curve's coefficients.
  TeX L1092, L1779–1784, L11150–11154.
- **VERIFIED (newform interfaces).** `PrintsAnalytic.IsNewformOf E f` uses a
  genuine normalized Tau Ceti `Newform N 2`, trivial nebentypus and
  equality of every positive-index coefficient with `lcoeff E`.
  `ModularNewform` supplies such an `f` at some positive level for every
  elliptic `E/ℚ`. `PrintsAnalytic.modularNewform_of_printed` derives it
  from `PoleS12.BCDTThmA` and the existing `RCLeaves` fields
  `shimuraConjugates`, `liMultiplicityOne`, `carayolEulerFactors`, and
  `faltingsRigidity`. Carayol and Faltings are GLUE readings.
  `CST.newformLevel E` is the infimum of the positive matching `Γ₀` cusp-form
  levels. The existing proof identifying the newform level with this
  infimum is independent of the conductor comparison.
- **VERIFIED (analytic interfaces).** `CloudB3RC53.IsLContinuation E F` is
  `Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s`.
  `Literature.IsLContinuation.eq` proves uniqueness for the identically
  defined predicate, and the active route has `PrintsAnalytic.isLContinuation_eq`
  and `PrintsAnalytic.eq_L_of_isLContinuation`. The latter identifies `F`
  with the uncompleted `ModularForm.L` of a matching newform.
  `AnalyticRankOne E` supplies such an `F` with `analyticOrderAt F 1 = 1`.
  The prior proof uses Mathlib's iterated derivative criterion to read
  this as `F 1 = 0 ∧ deriv F 1 ≠ 0`.
- **STANDARD (lead's source reading).** Gross–Zagier, Invent. Math. 84
  (1986), Thm (7.3)(1), p. 231, as restated p. 310. The p. 310 form
  applies to a matching weight-two newform at any level. The p. 231
  formulation explicitly uses a newform at the conductor. The page
  attribution follows the lead's source ruling. Independent scan check
  unverified here.
