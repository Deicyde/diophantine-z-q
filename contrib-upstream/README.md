# Contributions imported from upstream pull requests (unbuilt, pending review)

These files come from open pull requests by outside contributors in
[elliotglazer/diophantine-z-q](https://github.com/elliotglazer/diophantine-z-q). They were imported in
[Deicyde/diophantine-z-q#71](https://github.com/Deicyde/diophantine-z-q/pull/71) and a follow-up pull request, one commit per pull request,
authored by its contributor. Each file sits at `contrib-upstream/pr<N>/<its original path>`, where `<N>` is the
upstream pull request number.

**Nothing here is built, imported or run.** No Lake target, CI workflow or landing chain reads this directory,
so these modules have not been compiled against this repository, their axioms have not been checked, and their
imports still name their original paths. The Lean of `pr150/`, `pr70/`, `pr33/`, `pr22/`, `pr14/`, `pr6/` and `pr29/` (apart from their
`*Axioms.lean` and `lean/Checks/` audit files, which use `run_cmd`) had a static review: no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe`, `opaque`, or code that runs at build time. `pr15/`, `pr23/` and `pr27/` are research evidence
packets, kept as submitted: they contain comparator files that use `sorry`, compiled `.olean` files, zipped packets and, in
`pr23/.github/`, an edited copy of a workflow. That copy is inert: GitHub reads workflows only from the root `.github/`.

| directory | upstream pull request | contributor |
| --- | --- | --- |
| `pr150/` | [#150](https://github.com/elliotglazer/diophantine-z-q/pull/150) conditional total H10 reduction to rational polynomial solvability | loning |
| `pr70/` | [#70](https://github.com/elliotglazer/diophantine-z-q/pull/70) Hilbert/Serre support for five number-field D1 forms | loning |
| `pr33/` | [#33](https://github.com/elliotglazer/diophantine-z-q/pull/33) V15 retained-contact nonvanishing and trace quotient | loning |
| `pr22/` | [#22](https://github.com/elliotglazer/diophantine-z-q/pull/22) sqrt-two duplication cancellation helper | loning |
| `pr14/` | [#14](https://github.com/elliotglazer/diophantine-z-q/pull/14) simultaneous compact recurrence | loning |
| `pr6/` | [#6](https://github.com/elliotglazer/diophantine-z-q/pull/6) (with [#5](https://github.com/elliotglazer/diophantine-z-q/pull/5)) the frozen target's statement from eight explicit hypotheses; P₀ has infinite order | carlostoledo1891 |
| `pr29/` | [#29](https://github.com/elliotglazer/diophantine-z-q/pull/29) algebraic two-real-place application, stacked on #6 | loning |
| `pr15/` | [#15](https://github.com/elliotglazer/diophantine-z-q/pull/15) raw common-strict coordinates and integral-unit criterion (39 targets), with evidence | CheyLoveday |
| `pr23/` | [#23](https://github.com/elliotglazer/diophantine-z-q/pull/23) quadratic rows and durable tables for the quartic stack | cameronfreer |
| `pr27/` | [#27](https://github.com/elliotglazer/diophantine-z-q/pull/27) local conjugation, H¹ and boundary-comparison interfaces (41 roots), with evidence | CheyLoveday |

To use one of these in the proof, move it back to its original path (or under `ZInQKernel/Contrib/OneProof/`),
build it, and check its axioms. Every file each of these pull requests added or changed is here.
