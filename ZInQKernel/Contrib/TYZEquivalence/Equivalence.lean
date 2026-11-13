import ZInQKernel.Contrib.TYZEquivalence.CanonicalL

/-!
# The exact existential content of `PropN.TYZInputs`

The principal equivalence is the precise predicate proposed in
`docs/research/rv-pn-encoding.md` F1, using the *existing* statements and their
existing index conventions. It is not an unconditional proof of `TYZInputs`,
`TYZThm35ReadingA`, or an analytic continuation theorem.

The iff requires a continuation of order at most one only where the two genus
sums do not both vanish. The auxiliary reading-A equivalence makes this domain
explicit: reading A plus continuation existence on the nonzero parity support.
It deliberately does not replace this obligation with global
`Literature.HeckeContinuation`. A corollary separately records the sufficient
(but broader) existing Hecke assumption, without altering that assumption.
-/

noncomputable section

namespace ZInQ.PropN

open ZInQ.Literature ZInQ.RouteK.Rank5b TYZEquivalence

/-- Continuation existence on precisely the parity support forced by the
existential TYZ encoding. There is no obligation at both-even indices, nor at
zero, even, non-squarefree, or other-residue indices outside the stated domain. -/
def ParitySupportedContinuation : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → (T5aCl n ≠ 0 ∨ T5bCl n ≠ 0) →
    ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F

/-- The exact analytic obligation of `TYZInputs`, stated without an auxiliary
integer function or an abstract genus-point model. -/
def ParitySupportedOrderOne : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → (T5aCl n ≠ 0 ∨ T5bCl n ≠ 0) →
    ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1

/-- **The exact TYZ input equivalence.** At each squarefree class-5 index,
either a continuation of order at most one exists, or both genus sums vanish.
The reverse implication constructs one integer function simultaneously for all
indices; it does not assume `TYZInputs` through a `Fact` or any other binder. -/
theorem tyzInputs_iff :
    TYZInputs ↔ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      (∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧
        analyticOrderAt F 1 ≤ 1) ∨ (T5aCl n = 0 ∧ T5bCl n = 0) := by
  constructor
  · rintro ⟨L, hL1, h28, hI7, hG⟩ n hn hsq
    by_cases hLn : L n = 0
    · right
      obtain ⟨G⟩ := hG n hn hsq
      exact genusSums_eq_zero hL1 h28 hn hsq G hLn
    · exact Or.inl (hI7 n hn hsq hLn)
  · intro h
    refine ⟨canonicalL, canonicalL_one, canonicalL_lemmaTwoEight, ?_, ?_⟩
    · intro n hn hsq hLn
      rcases h n hn hsq with hF | hrows
      · exact hF
      · rcases (canonicalL_ne_zero_iff hn).mp hLn with ha | hb
        · exact (ha hrows.1).elim
        · exact (hb hrows.2).elim
    · intro n hn hsq
      exact canonicalL_genusData hn hsq

/-- The disjunctive predicate is exactly the order-one continuation condition
on the support of *either* row, not merely row 5b. -/
theorem tyzInputs_iff_supportedOrderOne : TYZInputs ↔ ParitySupportedOrderOne := by
  constructor
  · intro h n hn hsq hsupport
    rcases tyzInputs_iff.mp h n hn hsq with hF | hrows
    · exact hF
    · rcases hsupport with ha | hb
      · exact (ha hrows.1).elim
      · exact (hb hrows.2).elim
  · intro h
    apply tyzInputs_iff.mpr
    intro n hn hsq
    by_cases hrows : T5aCl n = 0 ∧ T5bCl n = 0
    · exact Or.inr hrows
    · left
      apply h n hn hsq
      by_cases ha : T5aCl n = 0
      · exact Or.inr (fun hb => hrows ⟨ha, hb⟩)
      · exact Or.inl ha

/-- Reading A and continuation existence on the parity support suffice for
order at most one there, with no continuation required off that support. -/
theorem supportedOrderOne_of_readingA (hA : TYZThm35ReadingA)
    (hC : ParitySupportedContinuation) : ParitySupportedOrderOne := by
  intro n hn hsq hsupport
  obtain ⟨F, hF⟩ := hC n hn hsq hsupport
  refine ⟨F, hF, ?_⟩
  by_contra hle
  have hrows := hA n hn hsq F hF (two_le_of_not_le_one hle)
  rcases hsupport with ha | hb
  · exact ha hrows.1
  · exact hb hrows.2

/-- **Reading A with the exact continuation domain.** Global
`HeckeContinuation` is not part of this equivalence. -/
theorem tyzInputs_iff_readingA_and_supportedContinuation :
    TYZInputs ↔ TYZThm35ReadingA ∧ ParitySupportedContinuation := by
  constructor
  · intro h
    refine ⟨tyzThm35ReadingA_of_tyzInputs h, ?_⟩
    intro n hn hsq hsupport
    obtain ⟨F, hF, -⟩ := tyzInputs_iff_supportedOrderOne.mp h n hn hsq hsupport
    exact ⟨F, hF⟩
  · rintro ⟨hA, hC⟩
    exact tyzInputs_iff_supportedOrderOne.mpr (supportedOrderOne_of_readingA hA hC)

/-- The existing broader Hecke premise gives the restricted continuation
obligation. Its range is kept unchanged and is not inferred from `TYZInputs`. -/
theorem supportedContinuation_of_hecke (hH : HeckeContinuation) : ParitySupportedContinuation := by
  intro n hn _ _
  exact hH n (by omega)

/-- Reading A with the existing Hecke continuation premise implies the input
encoding. This conditional implication is not a closed provider for either
literature premise or for `TYZInputs`. -/
theorem tyzInputs_of_readingA (hA : TYZThm35ReadingA) (hH : HeckeContinuation) : TYZInputs :=
  tyzInputs_iff_readingA_and_supportedContinuation.mpr ⟨hA, supportedContinuation_of_hecke hH⟩

/-- When the broader Hecke premise is included on *both* sides, the two TYZ
encodings are equivalent. This does not strengthen the principal iff. -/
theorem tyzInputs_and_hecke_iff :
    TYZInputs ∧ HeckeContinuation ↔ TYZThm35ReadingA ∧ HeckeContinuation := by
  constructor
  · rintro ⟨hT, hH⟩
    exact ⟨tyzThm35ReadingA_of_tyzInputs hT, hH⟩
  · rintro ⟨hA, hH⟩
    exact ⟨tyzInputs_of_readingA hA hH, hH⟩

end ZInQ.PropN
