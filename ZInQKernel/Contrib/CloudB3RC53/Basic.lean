import ZInQKernel.Contrib.OneProof.SelmerTwoPower

/-!
# RC53 blueprint: genuine objects used by the top-level argument for Theorem 5.3

Theorem 5.3 of `diophantine_zq.tex` (`hyp:RC`, the restricted converse) is
`ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine`. Its proof is Sections 7–9
(tex L1760–5744) with Appendices E–G (tex L6825–10935). This file collects the genuine Lean
objects that the top-level deduction of the proof talks about:

* `Adm ℓ`: the hypothesis domain of Theorem 5.3 (positive squarefree `ℓ ≡ 11 mod 12`, tex
  L1761–1762).
* `qtwist E d`: the quadratic twist `E^{(d)}` (`y² = x³ + d a₂ x² + d² a₄ x + d³ a₆` on the model
  obtained by completing the square), the `E^{(h)}` of tex L1830 and throughout.
* `AnalyticRank E r`: `ord_{s=1} L(E,s) = r` over Mathlib's `WeierstrassCurve.LSeries`, in the
  convention of `ZInQ.Manuscript.AnalyticRankOne` (`analyticRank_one_iff`).
* `completedL N F s = N^{s/2} (2π)^{-s} Γ(s) F(s)` and `RootNumber E w`: the functional equation
  `Λ(2 - s) = w Λ(s)` on the critical strip `0 < Re s < 2` (where `Γ` has no pole), for some level
  `N > 0` and some entire continuation of `L(E, s)`. The sign `w` is the root number of tex L1797.
* `ProductOrderGeTwo E k`: `ord_{s=1} L(E,s) L(E^{(k)},s) ≥ 2`, i.e. `L'(E/K, 1) = 0` for
  `K = ℚ(√k)` once `L(E,1) = 0` (tex L4321–4326, L5732–5741, with `L(E/K,s) = L(E,s) L(E^{(k)},s)`
  read as the definition of the left side; the base change `L`-function of `E/K` is not in
  Mathlib).

Nothing is assumed here; this file only defines.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open Complex

/-- The hypothesis domain of Theorem 5.3: `ℓ` positive, squarefree, `ℓ ≡ 11 (mod 12)`
(tex L1761–1762, L1005–1010). -/
def Adm (ℓ : ℕ) : Prop := 0 < ℓ ∧ Squarefree ℓ ∧ ℓ % 12 = 11

/-- The curve `E_ℓ : y² = x(x - ℓ)(x + 3ℓ)` of Section 7 (tex L1763), as a curve over `ℚ`. -/
abbrev Ecurve (ℓ : ℕ) : WeierstrassCurve ℚ := ZInQ.Manuscript.curve (ℓ : ℚ)

/-- **The quadratic twist `E^{(d)}`.** Completing the square writes `E` as
`y² = x³ + (b₂/4) x² + (b₄/2) x + b₆/4`; its twist by `d` is
`y² = x³ + d (b₂/4) x² + d² (b₄/2) x + d³ (b₆/4)`. For a model with `a₁ = a₃ = 0` (such as `E_ℓ`)
this is `y² = x³ + d a₂ x² + d² a₄ x + d³ a₆`; `qtwist E 1` is the completed-square model of `E`. -/
def qtwist (E : WeierstrassCurve ℚ) (d : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, d * E.b₂ / 4, 0, d ^ 2 * E.b₄ / 2, d ^ 3 * E.b₆ / 4⟩

/-- **`ord_{s=1} L(E, s) = r`**: some entire function agrees with Mathlib's `L`-series of `E` on
`Re s > 3/2` and vanishes to order exactly `r` at `s = 1` (the convention of
`ZInQ.Manuscript.AnalyticRankOne`). -/
def AnalyticRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = r

theorem analyticRank_one_iff (E : WeierstrassCurve ℚ) :
    AnalyticRank E 1 ↔ ZInQ.Manuscript.AnalyticRankOne E := by
  simp only [AnalyticRank, ZInQ.Manuscript.AnalyticRankOne, Nat.cast_one]

/-- An entire continuation of `L(E, s)`: differentiable on `ℂ` and equal to Mathlib's `L`-series
on `Re s > 3/2`. -/
def IsLContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- The completed `L`-function `Λ(s) = N^{s/2} (2π)^{-s} Γ(s) F(s)` attached to a level `N` and a
function `F` (to be an entire continuation of `L(E, s)`). -/
def completedL (N : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s

/-- **`E` has root number `w`**: for some level `N > 0` and some entire continuation `F` of
`L(E, s)`, the completed function satisfies `Λ(2 - s) = w Λ(s)` on the critical strip
`0 < Re s < 2`. (On the strip `Γ(s)` and `Γ(2 - s)` have no poles, so no convention for `Γ` at
its poles enters; the identity theorem extends the equation to all of `ℂ` for the genuine `Λ`.)
For the conductor `N` of `E` this is the functional equation of a modular elliptic curve, and `w`
is the global root number `w(E) ∈ {±1}` of tex L1797. -/
def RootNumber (E : WeierstrassCurve ℚ) (w : ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∃ F : ℂ → ℂ, IsLContinuation E F ∧
    ∀ s : ℂ, 0 < s.re → s.re < 2 → completedL N F (2 - s) = (w : ℂ) * completedL N F s

/-- **`ord_{s=1} L(E,s) L(E^{(k)},s) ≥ 2`**: some entire function agrees with the product of the
two `L`-series on `Re s > 3/2` and vanishes to order at least two at `s = 1`. With
`L(E/ℚ(√k), s) = L(E, s) L(E^{(k)}, s)` (tex L5739–5740) this is `L'(E/K, 1) = 0` when
`L(E/K, 1) = 0`, the hypothesis of Lemma `ex:arith-base-zero` (tex L4321–4326). -/
def ProductOrderGeTwo (E : WeierstrassCurve ℚ) (k : ℚ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s * (qtwist E k).LSeries s) ∧
    2 ≤ analyticOrderAt F 1

end ZInQ.Contrib.CloudB3RC53
