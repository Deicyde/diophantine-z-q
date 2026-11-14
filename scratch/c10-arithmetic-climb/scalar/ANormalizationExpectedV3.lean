import ZInQKernel.HDecomp.C10.C10
import ZInQKernel.HDecomp.Descent.ProjRep

/-!
# EXPECTED STATEMENTS v3 — `a σ` fixed-place normalization (DEFINITIONS ONLY)

**Statements only: no proofs, no `theorem`, no candidate.** This file exists to be elaborated
and then FROZEN by the independent reviewer; the candidate module will be written separately
and will prove these exact definitions without editing them.

Supersedes v2 (`BOUNDED-STATEMENT-PROPOSAL-v2.lean`, sha256 87c771cb…) and v1 (7b5d423b…),
both retained byte-unchanged. Aligned to the frozen contract
`CONTRACT-FREEZE-ASIGMA.md` sha256 262a767e8f7ae0cfc85d350f5083adb5a5bcb9eeeb674f4a6a9b7a6e607c9b40
and to the shape requirements R1-R5.

R1: the consumer-useful deliverable is the BUNDLE `T6`
(`∃ aQ`, exact `ρ`-image, `ha`-shaped cochain equation, and `d 1 = 1 → aQ 1 = 1` inside the
bundle). The per-value `∃!` (`T5`) is retained only as supporting branch rigidity, not as the
deliverable.
R2: the quartic multiplicativity is stated in `ℚ` — supplier language — and will be cast to
`ℝ` internally when the old real `GlueDescent.sign_normalization` is consumed.
R3: the `ℤ → ℚ → Qbar` sign coercion, the `Qbar` cast and the `(4 : ℕ)` exponent are explicit
named definitions below, so that elaboration is checked before any proof is attempted.
R4: `T6`'s cochain equation is `ha`-SHAPED. It is **not** the `GlueC10Link.c10_of_squares`
`ha` binder, and `qbarSign` is **not** the consumer's `ε`. Binding the common `C` to
`GlueC10.Qbar`, and binding the actual `c`/`ε` of B1, remain OPEN and need their own proofs.

## Non-claims, copied from the frozen contract

* No degree object is defined here and none exists in the canonical tree
  (`PkgI3.AbVar.IsIsogenyMor` is `IsFinite ∧ Surjective`); the degree data `d` is an explicit
  GIVEN rational input owned by the μ/B1 lane. No `AbVar.Hom.deg` provider is fabricated.
* No canonical `QuarticProp`/`Fact`-style leaf standing in for the quartic or the preimage.
* `a 1 = 1` and `ε 1 1 = 1` are NOT established unconditionally: they appear only under the
  explicit data `d 1 = 1` and `0 < c 1 1`.
* `C = GlueC10.Qbar` is not proved; the unit/field coercion bridge into the C10 consumer is a
  separate typed target, not included here.
* Local constancy and continuity of the given values are owned by 120c (176394) and are not
  touched.
* The candidate module will own its own scope and its own axiom reports; no axiom report from
  the character or β lanes is inherited.
* No topology on `ℚ̄`, no finite-image claim, no C10/H/H10 consequence.
-/

noncomputable section

namespace ClimbANormalizationExpected

open GlueDescent

/-! ## R3 — explicit coercions and the actual value, as named definitions -/

/-- The sign of a rational, as a rational: `ℤ → ℚ` on `SignType.sign`. -/
def ratSign (q : ℚ) : ℚ := ((SignType.sign q : ℤ) : ℚ)

/-- A rational in the common coefficient field `ℚ̄`. -/
def qbarOfRat (q : ℚ) : GlueC10.Qbar := (q : GlueC10.Qbar)

/-- The sign of a rational, in `ℚ̄`: the composite `ℤ → ℚ → ℚ̄`. NOT the consumer's `ε`. -/
def qbarSign (q : ℚ) : GlueC10.Qbar := qbarOfRat (ratSign q)

/-- The ACTUAL real normalization value of a positive rational degree, `d ^ (-(1/4))` with
Mathlib's real `rpow` — the same expression `GlueDescent.sign_normalization` uses. -/
def aReal (q : ℚ) : ℝ := (q : ℝ) ^ (-(1 / 4 : ℝ))

/-- Its complex value: the exact positive real image the fixed place must hit. -/
def aComplex (q : ℚ) : ℂ := ((aReal q : ℝ) : ℂ)

/-! ## Targets -/

/-- **T1 — the quartic equation comes from the actual `Real.rpow` definition**, not a `Fact`. -/
def QuarticFromRpow : Prop :=
  ∀ q : ℚ, 0 < q → 0 < aReal q ∧ (aReal q) ^ (4 : ℕ) * (q : ℝ) = 1

/-- **T2 — generalized fixed-place preimage (to be proved).** The character lane's compiled
`X ^ k - 1` lemma is insufficient; this is the statement for any value algebraic over `ℚ`. -/
def AlgebraicValueHasPreimage : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (f : K →+* ℂ) (z : ℂ),
    IsAlgebraic ℚ z → ∃ w : K, f w = z

/-- **T3 — the actual value is algebraic, GIVEN a rational degree.** Root of `C q * X ^ 4 - 1`.
False for an arbitrary positive real degree, which is why rationality is carried. -/
def RationalDegreeValueIsAlgebraic : Prop :=
  ∀ q : ℚ, 0 < q → IsAlgebraic ℚ (aComplex q)

/-- **T4 — the sign at the identity, ONLY from the explicit datum `0 < c 1 1`.** -/
def SignAtOneIsOne : Prop :=
  ∀ (G : Type) [Group G] (c : G → G → ℚ), 0 < c 1 1 → qbarSign (c 1 1) = 1

/-- **T5 — supporting branch rigidity (not the deliverable).** Exactly one element of `ℚ̄` has
the ACTUAL positive real value as its `ρ`-image; the quartic equation alone admits three more. -/
def FixedPlaceBranchUnique : Prop :=
  ∀ (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (q : ℚ), 0 < q → ∃! w : GlueC10.Qbar, ρ w = aComplex q

/-- **T6 (R1) — the bundled deliverable.** Given rational positive degrees, a nonvanishing
rational cocycle and the quartic multiplicativity IN `ℚ` (R2), there is a `ℚ̄`-valued `aQ`
whose `ρ`-image is exactly the actual positive real value, which satisfies the `ha`-SHAPED
cochain equation (R4: not the consumer's `ha`, and `qbarSign` is not the consumer's `ε`), and
which is normalized at `1` under the explicit datum `d 1 = 1`. -/
def BundledFixedPlaceNormalization : Prop :=
  ∀ (G : Type) [Group G] (ρ : GlueC10.Qbar →ₐ[ℚ] ℂ) (d : G → ℚ) (c : G → G → ℚ),
    (∀ g, 0 < d g) → (∀ g h, c g h ≠ 0) →
    (∀ g h, d g * d h = (c g h) ^ (4 : ℕ) * d (g * h)) →
    ∃ aQ : G → GlueC10.Qbar,
      (∀ g, ρ (aQ g) = aComplex (d g)) ∧
      (∀ g h, aQ g * aQ h * qbarOfRat (c g h) = qbarSign (c g h) * aQ (g * h)) ∧
      (d 1 = 1 → aQ 1 = 1)

end ClimbANormalizationExpected

/-! ## R3 elaboration checks — definitions only -/

#check @ClimbANormalizationExpected.ratSign
#check @ClimbANormalizationExpected.qbarOfRat
#check @ClimbANormalizationExpected.qbarSign
#check @ClimbANormalizationExpected.aReal
#check @ClimbANormalizationExpected.aComplex
#check @ClimbANormalizationExpected.QuarticFromRpow
#check @ClimbANormalizationExpected.AlgebraicValueHasPreimage
#check @ClimbANormalizationExpected.RationalDegreeValueIsAlgebraic
#check @ClimbANormalizationExpected.SignAtOneIsOne
#check @ClimbANormalizationExpected.FixedPlaceBranchUnique
#check @ClimbANormalizationExpected.BundledFixedPlaceNormalization
