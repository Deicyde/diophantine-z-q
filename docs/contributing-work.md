# Choosing useful contribution work

Read [project status](project-status.md), then [issue #37: open targets and claims](https://github.com/elliotglazer/diophantine-z-q/issues/37). [Lean contributions](lean-contributions.md), [CONTRIBUTING](../CONTRIBUTING.md) and [research review](research-review/README.md) remain the detailed rules; this checklist introduces no new acceptance policy.

## Pick and claim one consumer input

Read the exact theorem that will use your result. Inspect open PRs **and the development mirror** before assuming an input absent from main is unproved. Claim one bounded task in #37:

```text
Claiming <exact consumer binder/object> at <source revision>.
Reusing <supplier/PR and revision>; not duplicating <existing work>.
Scope/files: <...>. Remaining assumptions: <...>.
Branch/draft and planned checks: <...>.
```

Coordinate with an existing owner before touching their files; record a handoff or stop in the same tracker. Multi-agent work needs disjoint results/files, one owner per shared supplier, and one integration lane. Similar names, local/global variants and abstract models are not interchangeable.

**Completion test:** the intended consumer uses your actual constructed input at its exact type. Do not replace the needed object, map, basis or conclusion with an assumed Fact/axiom or another conditional wrapper.

## Start from current main; reuse rather than copy blindly

- Base new main PRs on current upstream main. Read or reuse bounded suppliers from `deicyde/kernel-formalization`, but do not base a PR on its diverged history.
- Put ordinary new proofs in `ZInQKernel/Contrib/`; keep notes outside that proof namespace, normally in `docs/research/`.
- Preserve supplier revisions, licenses/change notices, frozen definitions and toolchain pins. Use the existing opt-in Axiom bridge/cache rather than a second bridge or default-root dependency expansion.
- Identify definition/statement changes, added assumptions or weakened conclusions separately from proof-only work.
- For overlapping dependency sources, agree on the canonical version and integration order. Do not rewrite, retarget, close or reclaim another contributor's PR casually. A smaller consumer diff after dependencies land still needs checks on its new base.

## Check the actual tracked candidate

Build the named new modules, not only `lake build ZInQKernel`: the root may not import contributions. Include new source files in the git-tracked candidate before running the [full kernel/rejection checks](lean-contributions.md#build-and-audit).

Record exact base/head, commands, full elaborated types, actual bodies/axioms and results. A registered provider must have exactly its registered proposition, without extra explicit, implicit, instance, section or universe inputs; `P → P` or `[Fact P]` does not close P. Recognized proofs may use only `propext`, `Classical.choice` and `Quot.sound`.

For a changed application, check actual fields, primes, bases, maps, normalizations, exceptional cases and simultaneous parameter choices. Preserve failures and meaningful negative controls. Compilation, scoped replay, normal validation, non-author review, public CI and protected acceptance are separate stages.

## Submit and hand off one coherent package

The PR should answer four questions:

1. **Which consumer input is now supplied?** Give the exact declaration/object and before/after hypotheses.
2. **Which dependencies are reused?** Link their revisions and overlapping PRs; explain the canonical/shared source choice.
3. **What passed?** Name the source/CI revisions, type/body/axiom checks and review scope.
4. **What remains?** State unproved inputs and missing integration; do not label a helper, source map, registration or conditional reduction as complete H.

Prefer one coherent verified package over overlapping placeholder PRs or copied-dependency/status PRs. If distinct proof, statement or editorial review routes require a split, explain it. The required protected review must cover the exact final revision; a green build or contributor-written acceptance flag does not provide it. A new official polynomial record additionally needs the complete current TeX/PDF release process.

Update the #37 claim with the final revision/PR, actual result, remaining binders and agreed next scope. The integrator updates [project status](project-status.md) after checking the consumer and main state. Historical source, review and failed-attempt evidence remain intact.
