import Mathlib

/-!
# Pole completeness (PC)

Theorem 5.2 (`hyp:PC`) of the 11/5 manuscript. The manuscript derives it from the
restricted converse theorem (Theorem 5.3, `hyp:RC`), whose proof occupies Sections 7–9
and Appendices E–G and uses Kato's Euler system, Waldspurger's formula,
Bump–Friedberg–Hoffstein, Nekovář's Selmer complexes and Gross–Zagier–Kolyvagin.

This file uses the **Route K** pole polynomial (`docs/research/rv-route-k.md`): its two curves
are the congruent number curves `y² = x(x - ℓ)(x + ℓ)`, whereas the manuscript's `Q_pole` uses
`y² = x(x - ℓ)(x + 3ℓ)`. The soundness lemma (Lemma 5.1) holds verbatim for both
(`ZInQ.Mult.poleSystem_no_negative_odd_valuation`).

For Route K, PC is no longer a hypothesis of the main theorem: it is the theorem
`ZInQ.poleCompleteness_of_certifiedRank` (`ZInQKernel/RouteK/Assembly/PoleCompleteness.lean`),
proved from the narrower hypothesis CR₃ (`ZInQ.CertifiedRank`,
`ZInQKernel/Hypotheses/CertifiedRank.lean`) through the descent lemma
(`ZInQ.RouteK.descent_lemma`, `docs/research/slot-k.md` §2). This file keeps the definitions of the
polynomial and of PC, which the assembly and the variant
`exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness` use.
-/

namespace ZInQ

open scoped BigOperators

/-- The exceptional primes `S₀ = {2, 3, 5, 7, 13}` of the pole predicate. -/
def poleS0 : Finset ℕ := {2, 3, 5, 7, 13}

/-- The pole polynomial `Q_pole` of Section 5, evaluated at the input `B` and its eleven
witnesses `b₀, …, b₅, e, z, r₁, r₂, w`.

This is the **Route K** polynomial: `T₁ = A(A - e)(A + e)` and `T₂ = A(Az² - eH)(Az² + eH)`,
so that `(A, r₁)` lies on `y² = x(x - e)(x + e)` and `(Az², zr₂)` on
`y² = x(x - eH)(x + eH)` (the curve `x + ℓ`). The manuscript's `Q_pole` (lines 979–986) has
the factors `A + 3e` and `Az² + 3eH` instead (the curve `x + 3ℓ`). -/
def polePoly (B : ℚ) (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ) : ℚ :=
  let m := (1 - 2 * b 0) * (1 + b 1) * (1 + 2 * b 2) * (1 + 4 * b 3) * (1 + 6 * b 4) *
    (1 + 12 * b 5)
  let A := m * B
  let H := A * (A - B ^ 2)
  let T₁ := A * (A - e) * (A + e)
  let T₂ := A * (A * z ^ 2 - e * H) * (A * z ^ 2 + e * H)
  B * ((∑ i, (b i ^ 2 - b i) ^ 2) + (e * H * z * w - 1) ^ 2 + (r₁ ^ 2 - T₁) ^ 2 +
    (r₂ ^ 2 - T₂) ^ 2)

/-- `Φ(B)`: the pole polynomial has a rational zero with input `B`. The polynomial is the
Route K one (`polePoly`, curves `x + ℓ`); the manuscript's `Φ` uses its `Q_pole` with the
curves `x + 3ℓ`. -/
def PoleSoluble (B : ℚ) : Prop :=
  ∃ (b : Fin 6 → ℚ) (e z r₁ r₂ w : ℚ), polePoly B b e z r₁ r₂ w = 0

/-- **PC** (Theorem 5.2, pole completeness). Every rational `B` with square reduced
denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` for every `p ∈ S₀` satisfies `Φ(B)`.

Here `Φ` refers to the Route K pole polynomial `polePoly` (curves `y² = x(x - ℓ)(x + ℓ)`), not
to the manuscript's `Q_pole` (curves `y² = x(x - ℓ)(x + 3ℓ)`); the statement is otherwise the
manuscript's. In this form PC is a theorem from the hypothesis CR₃
(`ZInQ.poleCompleteness_of_certifiedRank`), not a hypothesis of the main theorem. -/
def PoleCompleteness : Prop :=
  ∀ B : ℚ, IsSquare B.den → 0 < B → B < 1 / 2 → (∀ p ∈ poleS0, 4 ≤ padicValRat p B) →
    PoleSoluble B

end ZInQ
