# P3: affine point-count formula at all primes

Contribution to **P3** of [issue #37](https://github.com/elliotglazer/diophantine-z-q/issues/37),
first proposed in PR #40 as commit `7985cdf`, independently based on
`deicyde/kernel-formalization` at `533aa66cc3485e21f2d90303e3a34f79d081722d`.
It is now proposed against `main`; see [Migration to `main`](#migration-to-main). No P1 or P2 dependency is introduced.

## Statements and proof

The declarations are in `ZInQ.Contrib.BadPrimes`.

`BadPrimes/Affine.lean` supplies two geometric counts:

1. Over any field, `t ↦ (t²,t³)` is a bijection onto the cusp `y² = x³`.
   Its inverse is `y/x`, with total field division taking value zero at the
   origin. Thus over a finite field the cusp has exactly `#F` affine solutions.
2. Over `ZMod 2`, every element satisfies `a² = a`. The equation
   `y² = x³ - d²*x` is consequently a graph over `x` and has exactly two
   solutions for every `d`.

`BadPrimes.lean` splits a prime divisor of `2*d` into `p = 2` or `p ∣ d`.
The binary graph applies in the first case. In the second, `d` is zero in
`ZMod p`, so the equation is the cusp. Therefore

```text
Nat.card { (x,y) : ZMod p × ZMod p | y² = x³ - d²*x } = p
```

at every bad prime, for every natural `d`.

The existing additive-reduction computation gives coefficient zero at bad
primes for odd squarefree `d`. Combining it with this count and the existing
good-prime point-count theorem proves `LFunction_cd_prime_eq_sub_card_all`:

```text
a_p(C_d) = p - number of all affine solutions
```

for **every prime**, with no good-prime assumption.

## Trust boundary

All affine counts include singular solutions. They are **not** counts of
Mathlib's nonsingular `WeierstrassCurve.Affine.Point` type. In particular,
one must not use the good-prime identity for that point type at a singular
reduction merely by adding a point at infinity.

The affine counts have no parity or squarefreeness restriction on `d`. The
`LFunction` comparison retains **oddness and squarefreeness**, matching the
original local-model computation. No original definition, frozen statement,
literature hypothesis, or original checker is changed.

## Original reproduction (base `533aa66`)

Lean **4.35.0**; Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build ZInQKernel
lake env lean scripts/check_bad_primes.lean
lake env lean scripts/print_axioms.lean
python3 scripts/check_target.py
git diff --check
```

The regressions cover the cusp in arbitrary characteristic, the binary count
for every `d`, singular `d = 0`, a prime dividing `d`, even `d`, and the
all-prime coefficient formula. The checker prints the transitive axiom
dependencies of the new public declarations.

## Original validation evidence (commit `7985cdf`)

`lake build ZInQKernel` passes (**9969 jobs**). The P3 regression file exits `0`
without diagnostics, and all **seven** new declarations, including both explicit
equivalences, report only `propext`, `Classical.choice`, and `Quot.sound`. The
original axiom script completes with **272/272** standard-only reports. The frozen
target, whitespace, and prohibited-proof-shortcut checks pass. The geometric
module emits three benign legacy-module import notices; no proof errors are
suppressed.

Proof-source SHA-256 values:

```text
fb5ba6348dfcd18e42fcdd125e964e600486ba672e78f4b23371221e894c5145  Affine.lean
915777a0cee64597e7a3af622ec24a12f3fb15dc402cb0d5554eb0fccafdf7ae  BadPrimes.lean
```

## Provenance

An agentcloud subagent supplied the cusp and binary-field proofs. The parent
agent supplied the bad-prime case split, the all-prime coefficient theorem,
and integration and regression checks. A separate reviewer approved the statements
and trust boundary and independently elaborated the exact proof and regression
sources through `lake env lean --stdin`, with exit code `0` and standard-only
axioms. Formal correctness is established by Lean's kernel, not by AI mathematical
confidence.

## Migration to `main`

Issue #37 now asks for PRs against `main`. This branch re-proposes the original PR #40 commit
`7985cdfb8121eff6ac05dff691482dfbb9305c5d` (base `533aa66cc3485e21f2d90303e3a34f79d081722d`) on `main` at `a5937595cde3e3db00975b81e5171cdef92c801a`.
These files are byte-identical to that commit:

```text
915777a0cee64597e7a3af622ec24a12f3fb15dc402cb0d5554eb0fccafdf7ae  ZInQKernel/Contrib/BadPrimes.lean
fb5ba6348dfcd18e42fcdd125e964e600486ba672e78f4b23371221e894c5145  ZInQKernel/Contrib/BadPrimes/Affine.lean
bcbe94a418e6d2c3d43f63edfa0affa735018a576d51a5c9ac3830b13f318b82  scripts/check_bad_primes.lean
```

On `main`, `ZInQKernel/RouteK/Rank/LFunctionCd.lean` and its project import, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` are byte-identical to the original base.
The only omitted original change is `import ZInQKernel.Contrib.BadPrimes` in `ZInQKernel.lean`, which is now a
locked baseline file. `scripts/check_kernel.py` builds every tracked contribution module
directly, so `lake build ZInQKernel` no longer builds this module. The unchanged header
comment of `scripts/check_bad_primes.lean` predates this and is superseded by:

```sh
lake exe cache get
lake build ZInQKernel.Contrib.BadPrimes
lake env lean scripts/check_bad_primes.lean
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
| Source hypotheses | No published theorem is newly applied. Mathlib field and `ZMod 2` facts and existing project theorems (`LFunction_cd_apply_prime_eq_sub_card`, `LFunction_cd_apply_prime_of_dvd`) are applied with every hypothesis discharged in Lean. |
| Constructed objects | The explicit equivalences `affineCuspEquiv` (`t ↦ (t², t³)`, inverse `y/x`) and `affineSquareTwoEquiv`; affine solution subtypes over `ZMod p`; the unchanged `LFunction`. |
| Domain and index coverage | Cusp: every field (any characteristic). Binary count: every `d`. Bad-prime count: every prime `p ∣ 2d`, every natural `d`. Coefficient formula: every prime, odd squarefree `d`, by a `p ∣ 2d` case split. |
| Transition and comparison maps | The two equivalences above, with total division at `x = 0`; the case split `p = 2` or `p ∣ d`. Fixed by elaborated types. |
| Identity of consumed object | Statements name the existing definitions directly; their files are byte-identical on `main` and at the original base. |
| Conventions | Affine counts include singular solutions and are not counts of Mathlib's nonsingular `Point` type. |
| Local conditions | Bad primes are exactly `p ∣ 2*d`; the coefficient at bad primes reuses the existing additive-reduction theorem. |
| Exceptional cases | Characteristic 2, `d = 0`, even `d`, and `p ∣ d` are regression cases. |
| Downstream consumption | No module on `main` imports this module; it closes no registered premise and does not change the headline. |

Statement fidelity, coverage, and closure require a non-author review of this revision and
remain **pending**. The reviewer approvals in the original sections above are preliminary, non-Astra reviews
of the original commit at its original base. They are not Astra acceptance and do not bind this
revision. No designated Astra reviewer has reviewed this branch.

Received findings: Preliminary review of the original regression file found that the concrete `p = 5` example lacked a `Fact (Nat.Prime 5)` instance; a local `have` was added before commit `7985cdf`. This affected one regression example, not the proof modules, and no mathematical failure was reported.

This is a proof-helper proposal, not a new polynomial record or research release, so the
TeX/PDF, cumulative handoff and mirror requirements do not apply. It adds no dependency, so no
cold/warm dependency benchmark is needed.
