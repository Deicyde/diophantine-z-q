# Gross–Zagier rank-one replacement: results log

- **VERIFIED (base).** Starting at `a28a93e98`. The outside-height arguments of
  `ZInQ.OneProof.frozenTarget` are `hRC : RestrictedConverseGenuine`,
  `hCT : CasselsTatePairingCurves`, `hB : BCDTThmAPrinted`, and
  `hK : KolyvaginThm1`. The assembly imports and uses the BCDT adapter.
- **VERIFIED (statements).** `HKRefereed.HKConsumed` is
  `∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → (PoleRC.SelM ℓ).ncard = 8 →
  PoleS12.IsModular (curve (ℓ : ℚ)) → AnalyticRankOne (curve (ℓ : ℚ)) →
  ∃ P : (curve (ℓ : ℚ)).toAffine.Point, ¬ IsOfFinAddOrder P`.
  `hkConsumed_of_hK` uses the rank projection; `poleCompleteness_of_hkConsumed`
  uses the point in `PoleRC.descentGlueM`. See `docs/research/hk-refereed.md`;
  manuscript L1005–1011, L1033–1069, L1072–1084, L1086–1097, L1111–1121.
- **VERIFIED (modularity interfaces).** `PoleS12.BCDTThmA` supplies a
  weight-two Γ₀ cusp form at some positive level with Mathlib's elliptic-curve
  coefficients. `BCDTPrint.BCDTThmAPrinted` is the Introduction's condition (2)
  at some positive level; `bcdtThmA_of_printed` forgets everything beyond the
  resulting matching Γ₀ cusp form. Neither statement fixes the arithmetic
  conductor. TeX L1092, L1779–1784, L11150–11154.
- **VERIFIED (newform interfaces).** `PrintsAnalytic.IsNewformOf E f` says
  trivial nebentypus and equality of all positive-index coefficients, for a
  genuine Tau Ceti `Newform N 2`. `ModularNewform` gives one at some positive
  level. `modularNewform_of_printed` uses BCDT and the four fields
  `RCLeaves.shimuraConjugates`, `liMultiplicityOne`, `carayolEulerFactors`,
  and `faltingsRigidity`; the last two are GLUE readings. The underlying
  `liCarayolNewformOfModular_of_printed_corollaries` retains the divisibility
  `M ∣ N`. `CST.newformLevel E` is the least positive matching Γ₀ cusp-form
  level; `ModularWeil.exists_form_at_newformLevel` attains it. The divisor
  information and trivial-character equivalence can pin the output to that
  least level. The least level's equality with the arithmetic conductor is
  not a definitional equality or a conclusion of those fields.
- **VERIFIED (analytic interfaces).** `CloudB3RC53.IsLContinuation E F` means
  `Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s`.
  The identically defined `Literature.IsLContinuation` has an identity-theorem
  proof `IsLContinuation.eq`; the active analytic route also has
  `PrintsAnalytic.eq_L_of_isLContinuation` for a matching newform.
  `AnalyticRankOne E` existentially packages such an `F` and
  `analyticOrderAt F 1 = 1`. Mathlib's
  `analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero` specializes to exactly
  the central value and derivative conditions.
- **STANDARD (locator from the reading desk, AI-READ):** Gross–Zagier,
  Invent. Math. 84 (1986), Thm (7.3)(1), p. 231. The stated standing
  assumption includes a matching weight-two newform at the conductor.
  No primary scan was independently checked here; the source status is
  draft pending the two-lens skeptic pass.
- **VERIFIED (source).** The existing
  `G0Prints.associatedGeometricConductorExponent` uses the true cohomological
  Tate representation, the local decomposition map, and `LadicCond.condExp`.
  Carayol's rational-newform corollary has separate analytic L and geometric
  conductor clauses. The narrower `RCLeaves.carayolEulerFactors` and
  `faltingsRigidity` only compare local Euler polynomials and do not carry
  conductor equality. The open application comparison is
  `PoleNewformLevelIsConductor`; no new source theorem is assumed for it.
- **VERIFIED (board and dependency source).** At the base the count is 31
  (9 LEAF / 22 GLUE). Before the restricted-converse fold this proposal
  replaces one row with six. Once the four newform suppliers are shared by
  the existing Theorem 5.3 assembly it replaces one row with two. The
  separate `Prints.kolyvagin` field remains in that assembly and has its
  own rank-zero uses. Neither scenario lowers the row or GLUE count.
- **VERIFIED (Lean).** Single-target import builds completed for
  `HKRefereedSubstitute`, `ModularNewformPrinted`, `WeakWeil`, `G0Prints.Carayol`,
  and `BCDTPrint.Descent`. Sequential `lake env lean` checks of
  `ZInQKernel/Contrib/OneProof/HKGZ73/Reduction.lean` and
  `scratch/hk-gz73/Check.lean` then passed without warnings on the final
  files. The scratch check composes the replacement with pole completeness
  and checks that the existing Theorem 5.3 forward input implies `hK`.
  `scratch/hk-gz73/axioms.txt` records the four new theorems, each with only
  `propext`, `Classical.choice`, and `Quot.sound`.
