# Local conjugation and boundary interfaces: upstream submission

Prepared for upstream on 10 November 2026 against upstream commit
`009b47f84ffe484a1cdbe187a75fe2c21b3df1f8` (Version 14). This is the current
reader entry for the combined contribution and its completed checking evidence.

The [connected fork review thread](https://github.com/CheyLoveday/diophantine-z-q/pull/3#issuecomment-6767745665)
holds the current reviewer handover and coordination. The source, specification,
application map, checks and essential evidence are in this repository. No
separate review pack or attachment is required.

## What this contributes

Four Lean modules prove three compatibility steps used in the construction of
derivative-switch functionals:

1. Derive the shared conjugation unit from the twisted representation and
   descend local evaluation and pullback to Mathlib's actual first group
   cohomology, retaining the distinct conjugate coefficient system.
2. Derive the cup coboundary correcting a local-condition representative to
   global localization, and remove that correction under a supplied chain trace.
3. Prove the degreewise cone comparison and show that a supplied right homotopy
   inverse preserves the common global projection and its localizations on
   homology.

The [specification](../../../research/local-boundary-interfaces/README.md),
[41-root inventory](../../../research/local-boundary-interfaces/TARGETS.json),
and [premise-to-theorem-to-consumer application map](../../../research/local-boundary-interfaces/APPLICATION.md)
state the exact hypotheses and remaining arithmetic inputs. Those are the
agreed conditional local interfaces; this submission does not assert the full
arithmetic determinant comparison or the main Diophantine theorem.

## Contribution and evidence are one submission

[Fork PR #2](https://github.com/CheyLoveday/diophantine-z-q/pull/2) supplied the
four modules and their original support, at reviewed head
`3e01aa877cd7434fdc759fe7b6a9271de6deff2e`. It is merged in the fork.
[Fork PR #3](https://github.com/CheyLoveday/diophantine-z-q/pull/3) supplied the
later evidence only, at `cdb1a92c41832b1631baf9391fd5f6b9c0c57157`.
It was merged into the fork at
`1e20a76a3c8abcc21235e1914231a7dd250cf908`; remote readback confirmed the
merged tree equals the reviewed evidence head. This submission includes both
selections. Fork integration and upstream acceptance remain distinct.

The completed evidence covers all four modules, all 41 selected roots and all
16 printed definitions. The retained Linux run's fresh Lean 4.35.0 build, transitive axiom audit,
source-bound export and all six checkers passed. The permitted axioms were
`propext`, `Quot.sound` and `Classical.choice`.

- [Latest evidence guide](openmath-os-evidence/PR_GUIDE.md)
- [Statement and application review](openmath-os-evidence/INDEPENDENT_STATEMENT_REVIEW.md)
- [Validation receipt](openmath-os-evidence/EVIDENCE_VALIDATION.json)
- [Complete six-checker output](openmath-os-evidence/paranoid.stdout.txt)
- [Retained export ZIP and payload identities](openmath-os-evidence/PACKET_ZIP.json)

The export contains 88,408,652 bytes and has SHA-256
`4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`.
Its selected roots and larger transitive dependency closure are distinguished
in the evidence guide. Checking took place in the documented Linux VM with
sandboxing; it is not an Open Math cloud run, protected comparator challenge,
hermetic dependency rebuild or external human specialist acceptance.

Earlier preparation documents and raw timeout/checkout logs retain their dated
status. Their then-pending checker statements are superseded by the completed
evidence linked above. No further run is waiting on those historical failures.

## Current base and retained source bindings

The four mathematical files and all 159 files selected from the combined fork
package are byte-identical to their source at `cdb1a92`. This entry and the
three files in [submission-review/](submission-review/) are the four additional
presentation/review files: **163 additions in total**, with no existing upstream
file modified. Source and evidence manifests, earlier review bindings and
receipts are preserved unchanged.

The application map remains explicitly anchored to Version 13 at
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. Its manuscript file and the Lean
toolchain, dependency lock and Lake configuration have unchanged bytes at the
new upstream base. The new bounded comparison checks the corresponding eleven
V14 passages: each has identical bytes, shifted by 773 lines. This comparison
does not rebind historical acceptance or review the entire V14 manuscript.

## Source-first coverage review

A distinct non-author reviewer reconstructed all 57 declarations and their
substantive suppliers from the four proof sources before reading the declared
inventory. The [frozen initial reconstruction](submission-review/SOURCE_USE_INITIAL.md)
records prior exposure; the [reconciliation and separate coverage decisions](submission-review/RECONCILIATION.md)
bind the 41 roots, 16 printed definitions, actual supplier uses and V13/V14
consumer passages. The [validation receipt](submission-review/VALIDATION.json)
contains the complete coverage index, passage hashes and fresh checks.

The reconciliation supplements two small omissions in the frozen application
map: the quotient-descent suppliers `LinearMap.liftOfSurjective` and
`LinearMap.equivOfSurjective_apply`, and the heading line of the derivative-switch
lemma. Both corrections are recorded there without editing historical files.
The review found no new proof defect in these conditional interfaces. Its
informal coverage and consumer-mapping decisions remain supporting evidence;
protected Astra/controller acceptance is unestablished.

This is an additive, non-release helper contribution. The current manuscript,
PDFs, construction artifacts, accepted Lean library, release records and prior
acceptances are not edited. No broader research packet is imported. These
preserved interfaces do not require completion of the remaining arithmetic
instance before being proposed as conditional helpers.

## Reproduction and remaining review

The original [native verification instructions](../../../research/local-boundary-interfaces/VERIFICATION.md)
and [Open Math handover](HANDOVER.md) remain available. Prepare a source-bound
project into a new directory with:

```sh
python3 -B scripts/prepare_local_boundary_openmath.py --output /tmp/local-boundary-verification-NEW
```

This command prepares inputs only. It does not build Lean or dispatch jobs;
its own `NOT_RUN` output describes that preparation invocation, not the status
of the completed checker evidence.

Current upstream review is governed by
[Protocol_D](../../research-review/PROTOCOL.md) and the
[Astra acceptance policy](../../research-review/ASTRA-REVIEW-POLICY.md).
The retained model reviews are supporting evidence, not an assertion of eligible
controller acceptance for a new upstream revision. Exact-revision hosted checks,
eligible Protocol_D v1.4 review and maintainer consideration remain required
before upstream merging. The controller must assess the exact published head,
base and merge revision using its trusted non-author Astra run records.
