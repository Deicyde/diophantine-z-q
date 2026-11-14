# Fixture taxonomy — a-normalization lane

Packaging metadata added after review. **No proof bytes were touched:** the candidate
(`ANormalizationCandidate.lean` `6419a901…`), the checks (`ANormalizationChecks.lean`
`afa1afc1…`), the frozen Expected (`ANormalizationExpected-v3.lean` `6f659cf6…`), the
retained first failures (`failed/…attempt1.lean` `cc9e7ffa…`, `897811dc…`) and every log
keep their exact bytes. The four fixture sources are unedited too; this file is the
authoritative reading of them.

## Two kinds of evidence, kept apart

**A. Proved necessity witnesses — mathematics, in `ANormalizationChecks.lean`.** These are
theorems, not fixtures:

| witness | what it proves |
|---|---|
| `quartic_fails_at_zero` | `¬ (0 < aReal 0 ∧ (aReal 0)^4 * ((0:ℚ):ℝ) = 1)`. Mathlib's real `rpow` is junk-valued at base `0`, so with positivity dropped **T1 is false**, not merely unprovable. |
| `quartic_admits_wrong_branch` | for `0 < q`, `(-(aReal q))^4 * q = 1` and `-(aReal q) ≠ aReal q`. A deliverable of the form `∃ a, a^4 * q = 1` **admits a wrong branch**; only the `ρ`-image equation of T5/T6 excludes it. |

**B. Structural fixtures — elaboration behaviour only, in `controls/`.** None of these is a
mathematical counterexample:

| fixture | cause type | shows | does NOT show |
|---|---|---|---|
| `BadNoQuartic.lean` | direct-term type mismatch | the ℚ-level quartic multiplicativity is load-bearing in the application: with it dropped the proved bundle does not inhabit the statement | that the conclusion is false without it |
| `BadNoPositivity.lean` | direct-term type mismatch | positivity of the degrees is load-bearing in the application | falsity — that is what the *proved* `quartic_fails_at_zero` gives, at `q = 0` |
| `BadSecondPlaceA.lean` | direct-term type mismatch | the bundle is tied to the ONE caller-fixed place `ρ` | that no `aQ` can satisfy two places at once |
| `BadNonClosedPreimage.lean` | instance-synthesis failure (`IsAlgClosed ℚ`) | algebraic closedness of the source field is load-bearing in T2 | an explicit value with no ℚ-preimage — none is constructed, and no transcendence argument is used anywhere in this lane |

## Wording that must travel with this packet

**Normalization is conditional.** `aQ 1 = 1` is delivered only under the explicit datum
`d 1 = 1`, and `qbarSign (c 1 1) = 1` only under the explicit datum `0 < c 1 1`. Neither is
established unconditionally, and nothing in the canonical tree supplies either: `sign_cocycle`
mentions normalization in its docstring only, exactly as `IsSignCocycle` does on the β side.

**The coefficient field is not the consumer's `C`.** The targets are stated over
`GlueC10.Qbar`. That `C = GlueC10.Qbar` for `GlueC10Link.c10_of_squares` is **not proved**;
T6's cochain equation is `ha`-SHAPED and is **not** the Link's `ha` binder; `qbarSign` is
**not** the consumer's `ε`, and `qbarOfRat ∘ c` is not the consumer's `c`. Identifying any of
those is open work with its own typed bridge, not a consequence of this lane.

**Degrees are given, never constructed.** There is no degree object in the canonical tree
(`PkgI3.AbVar.IsIsogenyMor` is `IsFinite ∧ Surjective`), and this lane defines none. `d` is a
GIVEN positive **rational** function, owned by the μ/B1 lane; rationality is load-bearing for
the preimage and is carried as a hypothesis, never inferred from a name. No `μ`, degree, B1,
Tate, native-point or global `Ψ` constructor appears here, and `rL` continuity remains
untouched with 120c (176394).

**Scope.** Conditional results only; no C10, no `H`, no height bound, no Hilbert 10.
