import ANormalizationCandidate

/-!
Independent type guard, plus two PROVED necessity witnesses.

Sections 1-6 restate each frozen target in full, without naming the Expected definition, and
close it with the candidate theorem. Section 7 proves two genuine mathematical facts about the
hypotheses (not structural fixtures): the positivity hypothesis is necessary, and the quartic
equation alone does not pin the branch.
-/

open ClimbANormalizationExpected ClimbANormalization

-- (1) T1
example : ∀ q : ℚ, 0 < q → 0 < aReal q ∧ (aReal q) ^ (4 : ℕ) * (q : ℝ) = 1 := quarticFromRpow

-- (2) T2
example : ∀ (K : Type) [Field K] [IsAlgClosed K] (f : K →+* ℂ) (z : ℂ),
    IsAlgebraic ℚ z → ∃ w : K, f w = z := algebraicValueHasPreimage

-- (3) T3
example : ∀ q : ℚ, 0 < q → IsAlgebraic ℚ (aComplex q) := rationalDegreeValueIsAlgebraic

-- (4) T4
example : ∀ (G : Type) [Group G] (c : G → G → ℚ), 0 < c 1 1 → qbarSign (c 1 1) = 1 :=
  signAtOneIsOne

-- (5) T5
example : ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (q : ℚ), 0 < q →
    ∃! w : GlueC10.Qbar, ρ w = aComplex q := fixedPlaceBranchUnique

-- (6) T6, the bundle
example : ∀ (G : Type) [Group G] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (d : G → ℚ) (c : G → G → ℚ),
    (∀ g, 0 < d g) → (∀ g h, c g h ≠ 0) →
    (∀ g h, d g * d h = (c g h) ^ (4 : ℕ) * d (g * h)) →
    ∃ aQ : G → GlueC10.Qbar,
      (∀ g, ρ (aQ g) = aComplex (d g)) ∧
      (∀ g h, aQ g * aQ h * qbarOfRat (c g h) = qbarSign (c g h) * aQ (g * h)) ∧
      (d 1 = 1 → aQ 1 = 1) := bundledFixedPlaceNormalization

-- (6') the frozen definitions are the ones proved
example : ClimbANormalizationExpected.QuarticFromRpow := quarticFromRpow
example : ClimbANormalizationExpected.AlgebraicValueHasPreimage := algebraicValueHasPreimage
example : ClimbANormalizationExpected.RationalDegreeValueIsAlgebraic :=
  rationalDegreeValueIsAlgebraic
example : ClimbANormalizationExpected.SignAtOneIsOne := signAtOneIsOne
example : ClimbANormalizationExpected.FixedPlaceBranchUnique := fixedPlaceBranchUnique
example : ClimbANormalizationExpected.BundledFixedPlaceNormalization :=
  bundledFixedPlaceNormalization

/-! ## 7. PROVED necessity witnesses (mathematical, not structural fixtures) -/

/-- **Positivity is necessary, not decorative.** Mathlib's real `rpow` is junk-valued at base
`0`, so at `q = 0` the quartic conclusion is FALSE: this is a genuine counterexample to the
statement with `0 < q` removed, not a guard-rejection. -/
theorem quartic_fails_at_zero :
    ¬ (0 < aReal 0 ∧ (aReal 0) ^ (4 : ℕ) * ((0 : ℚ) : ℝ) = 1) := by
  have h0 : aReal 0 = 0 := by
    rw [aReal, Rat.cast_zero]
    exact Real.zero_rpow (by norm_num)
  rintro ⟨hpos, -⟩
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **The quartic equation alone does not pin the branch.** For a positive rational degree the
negative root satisfies the same quartic equation and is a different number, so a deliverable
of the form `∃ a, a ^ 4 * q = 1` would admit a wrong branch; only the `ρ`-image equation of
T5/T6 excludes it. -/
theorem quartic_admits_wrong_branch {q : ℚ} (hq : 0 < q) :
    (-(aReal q)) ^ (4 : ℕ) * (q : ℝ) = 1 ∧ -(aReal q) ≠ aReal q := by
  have hp := (quarticFromRpow q hq).1
  have hq4 := (quarticFromRpow q hq).2
  constructor
  · calc (-(aReal q)) ^ (4 : ℕ) * (q : ℝ) = (aReal q) ^ (4 : ℕ) * (q : ℝ) := by ring
      _ = 1 := hq4
  · intro h
    linarith [h]

#print axioms quartic_fails_at_zero
#print axioms quartic_admits_wrong_branch
