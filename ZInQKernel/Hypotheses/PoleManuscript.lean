import Mathlib
import ZInQKernel.Hypotheses.Pole

/-!
# The manuscript's pole predicate: Theorem 5.2 and Theorem 5.3 as statements

The 11/5 manuscript's pole polynomial (`diophantine_zq.tex`, lines 973–1011) and its Theorems 5.2
and 5.3, in the namespace `ZInQ.Manuscript` (fork issue #74).

* `Manuscript.polePoly`, `Manuscript.PoleSoluble`, `Manuscript.PoleCompleteness`: the manuscript's
  `Q_pole`, `Φ` and **Theorem 5.2** (`hyp:PC`). Since fork issue #76 the main theorem's pole polynomial
  `ZInQ.polePoly` (`ZInQKernel/Hypotheses/Pole.lean`) is the manuscript's, with the curves
  `y² = x(x - ℓ)(x + 3ℓ)`, so these three are abbreviations of `ZInQ.polePoly`, `ZInQ.PoleSoluble`
  and `ZInQ.PoleCompleteness`: there is one definition. PC is a hypothesis of the headline
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`;
  `ZInQ.OneProof.frozenTarget` proves it from Theorem 5.3 (fork issue #83).
* `Manuscript.curve`, `Manuscript.AnalyticRankOne`, `Manuscript.RestrictedConverse`:
  **Theorem 5.3** (`hyp:RC`), the restricted converse from which the manuscript proves
  Theorem 5.2. Its Selmer condition is a parameter here, so that this file needs only Mathlib;
  the genuine instance is `SelmerTwoPower.RestrictedConverseGenuine`; see `RestrictedConverse`.
-/

namespace ZInQ.Manuscript

open scoped BigOperators

/-- The manuscript's pole polynomial `Q_pole` (Section 5, lines 976–982): an abbreviation of
`ZInQ.polePoly`, which is `Q_pole` with `T₁ = A(A - e)(A + 3e)` and `T₂ = A(Az² - eH)(Az² + 3eH)`. -/
abbrev polePoly (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) : ℚ :=
  ZInQ.polePoly B b e z r₁ r₂ w

/-- The manuscript's `Φ(B)`: an abbreviation of `ZInQ.PoleSoluble`. -/
abbrev PoleSoluble (B : ℚ) : Prop :=
  ZInQ.PoleSoluble B

/-- **Theorem 5.2 of the 11/5 manuscript (pole completeness, `hyp:PC`, lines 1001–1004).** Every
rational `B` with square reduced denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` for every
`p ∈ S₀ = {2, 3, 5, 7, 13}` satisfies `Φ(B)`. An abbreviation of `ZInQ.PoleCompleteness`. -/
abbrev PoleCompleteness : Prop :=
  ZInQ.PoleCompleteness

/-- The manuscript's `Q_pole` written out (lines 976–982) is `ZInQ.polePoly`. -/
theorem polePoly_eq (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) :
    polePoly B b e z r₁ r₂ w =
      let m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
        (1 + 12 * b 5)
      let A := m * B
      let H := A * (A - B ^ 2)
      let T₁ := A * (A - e) * (A + 3 * e)
      let T₂ := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + 3 * e * H)
      B * ((∑ i, (b i ^ 2 - b i) ^ 2) + (e * H * z * w - 1) ^ 2 + (r₁ ^ 2 - T₁) ^ 2 +
        (r₂ ^ 2 - T₂) ^ 2) :=
  rfl

/-- The manuscript's curve `E_ℓ : y² = x(x - ℓ)(x + 3ℓ) = x³ + 2ℓx² - 3ℓ²x`. -/
def curve (ℓ : ℚ) : WeierstrassCurve ℚ := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

/-- `c₄(E_ℓ) = 208ℓ²`, as the manuscript states after Theorem 5.3. -/
theorem curve_c₄ (ℓ : ℚ) : (curve ℓ).c₄ = 208 * ℓ ^ 2 := by
  simp only [curve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

/-- `Δ(E_ℓ) = 2304ℓ⁶`, as the manuscript states after Theorem 5.3. -/
theorem curve_Δ (ℓ : ℚ) : (curve ℓ).Δ = 2304 * ℓ ^ 6 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

/-- `ord_{s=1} L(E, s) = 1`: some entire function agrees with Mathlib's L-series of `E` on
`Re s > 3/2` and vanishes to order exactly one at `s = 1`. This is the convention of
`ZInQKernel/Hypotheses/CR3Literature.lean` (`IsLContinuation` with `analyticOrderAt`), written
out so that this file needs only Mathlib. -/
def AnalyticRankOne (E : WeierstrassCurve ℚ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = 1

/-- **Theorem 5.3 of the 11/5 manuscript (restricted converse, `hyp:RC`), with its Selmer
condition as a parameter.** For every positive squarefree `ℓ ≡ 11 (mod 12)`,
`corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` implies `ord_{s=1} L(E_ℓ, s) = 1`.

**A statement schema; the theorem is its genuine instance.** `SelmerCorankOne E` stands for
`corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = 1`. The `2`-primary Selmer group of an elliptic curve over `ℚ` and its
`ℤ₂`-corank are defined in `ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean` (over the vendored Tau
Ceti Galois cohomology), and Theorem 5.3 is the instance
`ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine := RestrictedConverse SelmerTwoPower.SelmerCorankOne`.
That instance is the hypothesis `ZInQ.OneProof.frozenTarget` takes, in place of `PoleCompleteness`
(fork issue #83). `RestrictedConverse P` is Theorem 5.3 only for that one predicate; it must not be
taken as a hypothesis at any other instance. -/
def RestrictedConverse (SelmerCorankOne : WeierstrassCurve ℚ → Prop) : Prop :=
  ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 →
    SelmerCorankOne (curve ℓ) → AnalyticRankOne (curve ℓ)

end ZInQ.Manuscript
