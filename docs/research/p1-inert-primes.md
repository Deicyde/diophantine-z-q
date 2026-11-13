# P1: zero coefficients at primes congruent to 3 modulo 4

Contribution to **P1** of [issue #37](https://github.com/elliotglazer/diophantine-z-q/issues/37),
first proposed in PR #39 as commit `87c7160`, independently based on
`deicyde/kernel-formalization` at `533aa66cc3485e21f2d90303e3a34f79d081722d`.
It is now proposed against `main`; see [Migration to `main`](#migration-to-main). It does not depend on the P2 contribution.

## Statements and proof

The new declarations are in `ZInQ.Contrib.InertPrimes`.

`InertPrimes/PointCount.lean` first proves a finite-field lemma: if `-1` is a
nonsquare and `f(-x) = -f(x)`, then the equation `y² = f(x)` has exactly `#F`
affine solutions. Negation permutes the quadratic-character sum and changes its
sign, so that sum is zero. Mathlib's square-root fiber formula then gives the count.
For `F = ZMod p`, `p % 4 = 3` makes `-1` a nonsquare. The function
`x³ - d²*x` is odd for every `d`, including `d = 0`.

`InertPrimes.lean` applies that count to the existing congruent-number model:

- `natCard_cdPoint_of_mod_four_three`: at good primes, the nonsingular projective
  point count is `p + 1`, including the point at infinity.
- `cdEulerPoly_eq_one_add_of_mod_four_three`: the good-prime Euler polynomial is
  `1 + p*T²`.
- `LFunction_cd_prime_eq_zero_of_mod_four_three_of_not_dvd`: at good primes,
  Mathlib's coefficient is zero.
- `LFunction_cd_prime_eq_zero_of_mod_four_three`: the coefficient also vanishes
  without a good-prime assumption, by combining this with the existing
  bad-prime additive-reduction computation.

The affine count holds for every natural `d`. The `LFunction` statements retain
**oddness and squarefreeness**, as required by the original model computation.
The projective `Point` count requires `p ∤ 2*d`: Mathlib's point type excludes
singular points, so the good-prime formula must not be extended to bad primes
merely by adding a point at infinity to the all-affine count.

## Original reproduction (base `533aa66`)

Lean **4.35.0**; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build ZInQKernel
lake env lean scripts/check_inert_primes.lean
lake env lean scripts/print_axioms.lean
python3 scripts/check_target.py
git diff --check
```

The regression file checks generic parameter scope, the singular affine case
`d = 0`, a good-prime projective count, Euler-polynomial simplification, and a
bad-prime coefficient. It prints axiom dependencies for all seven new declarations.
No original coefficient definition, frozen statement, literature hypothesis, or
original check script is changed.

## Original validation evidence (commit `87c7160`)

`lake build ZInQKernel` passes (**9969 jobs**). The P1 regression file exits `0`,
and all **seven** new declarations report only `propext`, `Classical.choice`, and
`Quot.sound`. The original axiom script completes with **272/272** standard-only
reports, and the frozen-target and whitespace checks pass. The point-count module
emits three benign legacy-module import warnings; no proof error is suppressed.

Proof-source SHA-256 values:

```text
7f3f6d1a102666deec24832f3c84503b425dd06193b5fba144cb62d3e921057f  PointCount.lean
91bd729f5650ad85cf7cc93fafb1f75d441b4cd85c716404dd66988850621ebf  InertPrimes.lean
```

## Provenance

An agentcloud implementation subagent supplied the finite-field proof; the parent
agent supplied the curve corollaries, integration and regression checks. A separate
reviewer approved statement fidelity and the trust boundary and independently
elaborated the exact sources and regression body through `lake env lean --stdin`
with exit code `0` and standard-only axioms. The proof is checked by Lean's kernel,
not accepted on AI mathematical confidence.

## Migration to `main`

Issue #37 now asks for PRs against `main`. This branch re-proposes the original PR #39 commit
`87c7160f457df93e58c4b564dfa04668576447d8` (base `533aa66cc3485e21f2d90303e3a34f79d081722d`) on `main` at `a5937595cde3e3db00975b81e5171cdef92c801a`.
These files are byte-identical to that commit:

```text
91bd729f5650ad85cf7cc93fafb1f75d441b4cd85c716404dd66988850621ebf  ZInQKernel/Contrib/InertPrimes.lean
7f3f6d1a102666deec24832f3c84503b425dd06193b5fba144cb62d3e921057f  ZInQKernel/Contrib/InertPrimes/PointCount.lean
4c0a5175a6847265e197bcc029f40ba870a2f318b94ef3bf7a92b7ff23f39e02  scripts/check_inert_primes.lean
```

On `main`, `ZInQKernel/RouteK/Rank/LFunctionCd.lean` and its project import, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` are byte-identical to the original base.
The only omitted original change is `import ZInQKernel.Contrib.InertPrimes` in `ZInQKernel.lean`, which is now a
locked baseline file. `scripts/check_kernel.py` builds every tracked contribution module
directly, so `lake build ZInQKernel` no longer builds this module. The unchanged header
comment of `scripts/check_inert_primes.lean` predates this and is superseded by:

```sh
lake exe cache get
lake build ZInQKernel.Contrib.InertPrimes
lake env lean scripts/check_inert_primes.lean
python -B scripts/test_kernel_audit.py
python -B scripts/check_kernel.py
git diff --check
```

`scripts/print_axioms.lean` and its 272 reports belong to the original base; `main` removed it.
The kernel audit replays every project declaration, including these, and rejects axioms other
than `propext`, `Classical.choice` and `Quot.sound`. Results for the exact PR head are reported
in the PR description, since this file cannot record its own commit.

## Review status and limits

These are direct kernel-checked Lean proofs about existing definitions, using Mathlib and
existing project theorems; they introduce no new published-theorem application.
The nine application obligations:

| Obligation | Status on this branch |
|---|---|
| Source hypotheses | No published theorem is newly applied. Mathlib lemmas (`quadraticChar_card_sqrts`, `quadraticChar_neg_one_iff_not_isSquare`, `FiniteField.isSquare_neg_one_iff`, `FiniteField.isSquare_of_char_two`) and existing project theorems (`natCard_point_shortCurve_zmod`, `LFunction_cd_apply_prime_eq_sub_card`, `LFunction_cd_apply_prime_of_dvd`, `cdModel_eq_shortCurve`) are applied with every hypothesis discharged in Lean. |
| Constructed objects | `ZMod p`, the subtype of affine solutions of `y² = x³ - d²x`, Mathlib's `Point` type of `shortCurve (-(d : ZMod p) ^ 2)`, and the unchanged `cdEulerPoly` and `LFunction`. |
| Domain and index coverage | Affine count: every natural `d` and prime `p ≡ 3 (mod 4)`. Point count and Euler polynomial: additionally `p ∤ 2d`. Vanishing: every prime `p ≡ 3 (mod 4)` for odd squarefree `d`, by a `p ∣ 2d` case split. |
| Transition and comparison maps | Fiber decomposition `Equiv.subtypeProdEquivSigmaSubtype`, negation `Equiv.neg`, and the existing affine-to-`Point` count (point at infinity). Fixed by elaborated types. |
| Identity of consumed object | Statements name the existing definitions directly; their files are byte-identical on `main` and at the original base. |
| Conventions | ℤ coefficients; `Point` excludes singular points, so the projective count requires `p ∤ 2d`. |
| Local conditions | Good versus bad reduction is the existing `p ∣ 2*d` split; the bad case reuses the existing additive-reduction theorem. |
| Exceptional cases | `d = 0`, `p ∣ d`, and the bad prime `3` of `d = 3` are regression cases; `p = 2` is excluded by `p % 4 = 3`. |
| Downstream consumption | No module on `main` imports this module; it closes no registered premise and does not change the headline. |

Statement fidelity, coverage, and closure require a non-author review of this revision and
remain **pending**. The reviewer approvals in the original sections above are preliminary, non-Astra reviews
of the original commit at its original base. They are not Astra acceptance and do not bind this
revision. No designated Astra reviewer has reviewed this branch.

Received findings: Preliminary review of the original regression file found that `decide` could not unfold the concrete `Squarefree 3`; it was replaced by `Nat.prime_three.squarefree` before commit `87c7160`. This affected one regression line, not the proof modules, and no mathematical failure was reported.

This is a proof-helper proposal, not a new polynomial record or research release, so the
TeX/PDF, cumulative handoff and mirror requirements do not apply. It adds no dependency, so no
cold/warm dependency benchmark is needed.
