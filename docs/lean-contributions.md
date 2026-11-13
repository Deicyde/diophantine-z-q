# Contributing to the Lean formalization

The root Lake project contains `ZInQKernel` and the vendored Green–Tao development.
The earlier accepted helper library remains in `lean/`. Both use the committed
Lean 4.35.0 and Mathlib revisions. Do not update these pins incidentally to a proof.

## Current mathematical scope

The root headline proves the original existential statement about an integer
polynomial in 292,890,231,905 variables from five premises:

| Premise | Existing declaration | Exact proof provider recognized by CI |
|---|---|---|
| Six-contact height estimate | `ZInQ.SixContactMin` | `ZInQ.Contrib.sixContactMin` |
| Tian–Yuan–Zhang input | `ZInQ.Literature.TYZThm35ReadingA` | `ZInQ.Contrib.tyzThm35ReadingA` |
| Analytic continuation | `ZInQ.Literature.HeckeContinuation` | `ZInQ.Contrib.heckeContinuation` |
| Functional equation | `ZInQ.Literature.FunctionalEquation5` | `ZInQ.Contrib.functionalEquation5` |
| Gross–Zagier input | `ZInQ.Literature.GrossZagier` | `ZInQ.Contrib.grossZagier` |

This does not formalize the current explicit quartic. A reduction to a published
theorem does not prove that theorem in Lean. The height decomposition is a work
plan; its named propositions are not automatically proved or independent leaves.
The scratch leaf file described in `docs/research/h-decomposition.md` is not in
this checkout. This registry does not claim to expose its contents.

## Submit a focused proof

Put new proof modules under `ZInQKernel/Contrib/`, with imports of the specific
definitions and lemmas they use. CI builds every tracked contribution module,
even if no root file imports it. Ordinary helper lemmas are welcome; they do not
need a registered provider name. Coordinate with the relevant tracker before
duplicating another contributor's proof.

To close a registered premise, provide a closed theorem with the corresponding
provider name and exactly the listed proposition as its type. No additional
explicit, implicit, typeclass or section hypotheses are allowed. A theorem of
type `P → P`, or one requiring `[Fact P]`, does not close `P`. CI checks the full
elaborated type, not the spelling of the theorem or the absence of `sorry` text.
The status table marks a premise proved only when this test and the kernel/axiom
checks pass. Removing it from the headline requires a checked discharge theorem.

Keep statement changes separate and explain why they are needed. The baseline
lock includes definitions used by the target, the existing source tree, compiler
pins and audit code. Changing a lock routes the PR to statement or infrastructure
review. It does not automatically reject a legitimate improvement. The protected
reviewer compares with the trusted base; updating your own manifest cannot give
your change approval.

For such a change, `python -B scripts/check_kernel_contract.py --write` rehashes
the pinned files, registers new baseline modules and drops deleted ones. It leaves
the targets, headline and exports unchanged. Review the resulting manifest diff
like any other lock change.

## Build and audit

From the repository root:

```sh
lake exe cache get
python -B scripts/test_kernel_audit.py
python -B scripts/check_kernel.py
```

`Kernel Lean build and audit` builds both root libraries and every tracked module,
checks the original frozen target, and replays project declarations through Lean's
kernel. It checks the actual dependency bodies for axioms outside `propext`,
`Classical.choice` and `Quot.sound`. The original quarantined frozen file is a
statement reference and is not imported as a proof. Runtime `unsafe` and `partial`
declarations are reported separately, as Lean's replay does not certify their
executable bodies. They cannot supply a recognized proof provider.

CI uploads the exact headline type, premise status, source-contract identity and
timings. When available, it compares against an authenticated successful main-push
report for the base commit. Missing base evidence is shown as **not measured**.
It is never treated as a count of zero proofs or as progress.

The build cache contains only root `.lake/build` outputs. Cache writes occur on
successful main pushes. The pinned Mathlib cache is fetched separately; toolchains
and dependency trees are not archived in the project cache. Cached project
declarations are still replayed and axiom-checked. New large dependencies need a
measured cold build and warm rebuild before integration. Prefer the narrow module
that supplies a theorem to a project's umbrella import.

## Acceptance

The public repository retains its required independent Astra check and up-to-date
branch requirement. There is no mandatory second human or CODEOWNERS approval.
An automated queue may identify proof-only PRs for a narrower review, but queuing,
compilation and a green status table do not publish the Astra acceptance check.
An eligible independent reviewer must review the exact revision and the applicable
Protocol_D obligations, including statement fidelity, provenance, dependency use
and any audit objections. The existing protected controller publishes acceptance
only from the authenticated review process.

Proof-only PRs need not rewrite the manuscript. A PR promoting a new polynomial
record still needs the complete current TeX and matching PDF required by
`docs/release-policy.md`. Licenses and third-party attribution remain as stated
in the repository; this infrastructure change grants no new license.
