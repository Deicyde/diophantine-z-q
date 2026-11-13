# P2: coefficient API for the congruent-number curves

This contribution addresses target **P2** of
[issue #37](https://github.com/elliotglazer/diophantine-z-q/issues/37).
It was first proposed in PR #38 as commit `70788a0`, based on
`deicyde/kernel-formalization` at `533aa66cc3485e21f2d90303e3a34f79d081722d`.
It is now proposed against `main`; see [Migration to `main`](#migration-to-main).

## Scope

`ZInQKernel/Contrib/CdCoeff.lean` imports the new API. On `main` it is built as a
tracked contribution module and is not imported by `ZInQKernel.lean`. The declarations are in `ZInQ.Contrib.CdCoeff` and use
the existing `ZInQ.Literature.cdCoeff` definition without changing it.

- `Core.lean` supplies the zero and one coefficients, coprime multiplicativity,
  the prime-power formula, the prime point-count formula, and vanishing at all
  multiples of bad primes. `cdArith` packages the coefficients as Mathlib's
  `ArithmeticFunction ℤ` and is proved multiplicative.
- `Recurrence.lean` supplies the good-prime recurrence
  `c(k+2) = a_p * c(k+1) - p * c(k)`, both with `a_p = cdCoeff d p` and
  with `a_p = p + 1 - #C_d(𝔽_p)`.
- `scripts/check_cdcoeff.lean` checks the public types, boundary cases, and
  transitive axiom dependencies.

These coefficient identities hold for **every natural-number parameter `d`**.
The comparison `cdCoeff_eq_LFunction` with Mathlib's elliptic-curve `LFunction`
retains the existing **odd and squarefree** assumptions. This distinction is
intentional: the Euler polynomial used by `cdCoeff` is not a computation of
the minimal model's local factor for arbitrary `d`.

## Proof and trust boundary

Multiplicativity uses disjoint prime factorizations of coprime natural numbers.
The prime-power formula uses the factorization of `p^k` and the inverse Euler
polynomial's constant coefficient `1`. At a bad prime the Euler polynomial
is `1`, so every positive-degree inverse coefficient vanishes. At a good
prime the quadratic Euler polynomial times its formal power-series inverse
is `1`; extracting the coefficient of degree `k+2` gives the recurrence.

No frozen target, literature hypothesis, or original check script is changed.
This API does **not** discharge the six-contact estimate, Hecke continuation,
the functional equation, Gross–Zagier, or the Tian–Yuan–Zhang hypothesis.

## Original reproduction (base `533aa66`)

The toolchain is Lean **4.35.0**, with Mathlib pinned by `lake-manifest.json` to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build ZInQKernel
lake env lean scripts/check_cdcoeff.lean
lake env lean scripts/print_axioms.lean
python3 scripts/check_target.py
git diff --check
```

## Original validation evidence (commit `70788a0`)

The full `lake build ZInQKernel` passes (**9970 jobs**), including the new
umbrella import. The original `scripts/print_axioms.lean` completes, and all
**272 requested reports** contain only the three permitted standard axioms.
`python3 scripts/check_target.py` confirms the frozen statement matches its
reference token for token. `git diff --check` passes. Existing module-system,
deprecation, and linter warnings remain in unchanged source files; the new
proof modules compile without diagnostics.

The contribution umbrella builds successfully, and `scripts/check_cdcoeff.lean`
exits with code `0`. All **22 new declarations**, including the arithmetic-function
wrapper and successor-exponent vanishing corollary, report only `propext`,
`Classical.choice`, and `Quot.sound` as transitive axiom dependencies.

An independent reviewer approved the statement fidelity and trust boundary and
separately elaborated the exact proof sources together with the regression body
using `lake env lean --stdin`, without relying on the new modules' compiled outputs.
That independent elaboration also exited with code `0`.

Proof-source SHA-256 values:

```text
fa2175d2f6eea684d36a7badaf01699b3d21ca8aea9e520acd236cc937149ab1  Core.lean
8a96e9598d72434cc6d2171cffdaed400e2d5ad693c3fe11bc3a7767fe91f42e  Recurrence.lean
```

## Provenance

An agentcloud agent split the proof work between two independent implementation
agents, integrated the modules and regression checks, and obtained an independent
review. The claims of formal correctness rest on Lean compilation and the axiom
reports, not on the agents' mathematical confidence.

## Migration to `main`

Issue #37 now asks for PRs against `main`. This branch re-proposes the original PR #38 commit
`70788a03273a5b3d87d6ff14aac2ff9b98f7faef` (base `533aa66cc3485e21f2d90303e3a34f79d081722d`) on `main` at `a5937595cde3e3db00975b81e5171cdef92c801a`.
These files are byte-identical to that commit:

```text
5c68d9a8e45693afa2b45b4dc9743d78a97dc0acf8222d7c75dd8ddf42142122  ZInQKernel/Contrib/CdCoeff.lean
fa2175d2f6eea684d36a7badaf01699b3d21ca8aea9e520acd236cc937149ab1  ZInQKernel/Contrib/CdCoeff/Core.lean
8a96e9598d72434cc6d2171cffdaed400e2d5ad693c3fe11bc3a7767fe91f42e  ZInQKernel/Contrib/CdCoeff/Recurrence.lean
b2132627ca3db8c6222914e1b3440fa6275841a25513114f76205a431716cd13  scripts/check_cdcoeff.lean
```

On `main`, `ZInQKernel/RouteK/Rank/LFunctionCd.lean` and its project import, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` are byte-identical to the original base.
The only omitted original change is `import ZInQKernel.Contrib.CdCoeff` in `ZInQKernel.lean`, which is now a
locked baseline file. `scripts/check_kernel.py` builds every tracked contribution module
directly, so `lake build ZInQKernel` no longer builds this module. The unchanged header
comment of `scripts/check_cdcoeff.lean` predates this and is superseded by:

```sh
lake exe cache get
lake build ZInQKernel.Contrib.CdCoeff
lake env lean scripts/check_cdcoeff.lean
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
| Source hypotheses | No published theorem is newly applied. Mathlib lemmas (`Nat.factorization_mul_of_coprime`, `PowerSeries.invOfUnit`/`mul_invOfUnit`, `ArithmeticFunction.IsMultiplicative`) and existing project theorems (`LFunction_cd_apply`, `natCard_point_shortCurve_zmod`, `cdEulerPoly_coeff_zero`, `coeff_one_invOfUnit`, `cdModel_eq_shortCurve`) are applied with every hypothesis discharged in Lean. |
| Constructed objects | The unchanged `ZInQ.Literature.cdCoeff`, `cdEulerPoly`, `cdModel` and Mathlib `LFunction`; the new `cdArith d : ArithmeticFunction ℤ` is a wrapper with `cdArith_apply` by `rfl`. |
| Domain and index coverage | Coefficient identities: every natural `d`, every `n`/prime `p`/exponent `k` as stated; `LFunction` comparison: odd squarefree `d`, every `n`. Bad/good split is `p ∣ 2*d`. |
| Transition and comparison maps | Coefficient extraction from `cdEulerPoly * invOfUnit = 1` (degree `k+2`); `a_p = p + 1 - #C_d(𝔽_p)` via the existing point-count theorem. Signs and casts are fixed by the elaborated types. |
| Identity of consumed object | Statements name the existing definitions directly; the defining files are byte-identical on `main` and at the original base. |
| Conventions | ℤ coefficients; Mathlib's `LFunction` of `shortCurve (-(d:ℚ)^2)`; `Point` counts include the point at infinity and exclude singular points. |
| Local conditions | Good/bad reduction enters only through the existing `p ∣ 2*d` split and model computation. |
| Exceptional cases | `n = 0`, `n = 1`, `d = 0`, bad primes and exponent `0` are separate theorems or regression cases. |
| Downstream consumption | No module on `main` imports this API; it closes no registered premise and does not change the headline. |

Statement fidelity, coverage, and closure require a non-author review of this revision and
remain **pending**. The reviewer approvals in the original sections above are preliminary, non-Astra reviews
of the original commit at its original base. They are not Astra acceptance and do not bind this
revision. No designated Astra reviewer has reviewed this branch.

Received findings: No substantive finding was received on PR #38's mathematics or regression file.

This is a proof-helper proposal, not a new polynomial record or research release, so the
TeX/PDF, cumulative handoff and mirror requirements do not apply. It adds no dependency, so no
cold/warm dependency benchmark is needed.
