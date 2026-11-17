# PR #15 retained-comparator preparation review

**No blocking findings in the bounded preparation scope. Compilation, comparator and paranoid execution remain NOT_RUN pending Open Math OS.** This is a non-author source/preparation review, **not protected-controller acceptance**, mathematical acceptance, release qualification or permission to merge.

Reviewed on 10 November 2026 by Codex agent `/root/retained_comparator_review`, requested model `gpt-6-astra`. The requested identity is not a provider attestation or evidence of protected-controller eligibility. I did not author or repair the contribution. I read the source contracts before the candidate Challenge, then inspected the proposed support and author validation evidence. Parent context, model and toolchain limitations are shared; a separately running reviewer does not eliminate those limitations.

The checkout was `7c178b3edaf7f1ca9c91d542c3453bfdbaea73f3` with new support uncommitted. [PREPARATION_REVIEW_INPUTS.json](PREPARATION_REVIEW_INPUTS.json) binds every reviewed contribution/input, contextual source, pinned comparator source and prepared-project file by SHA-256. These byte bindings, not a claim that the baseline commit contained the new files, define this review's revision.

Reader route: [execution and return handoff](HANDOFF.md), [author offline validation](LOCAL_VALIDATION.json), and [exact review bindings and independent checks](PREPARATION_REVIEW_INPUTS.json).

## Source and comparator selection

The existing PR15 Challenge and comparator configuration remain byte-identical to the request's frozen inputs. The 39 mathematical targets are all theorem targets; there are no definition holes. I checked the unchanged base preparer and its source-copy generator, the three frozen-manifest gates, new retention preparer, export inventory and complete prepared output. This review does not re-open or extend the earlier mathematical acceptance.

I inspected the installed Lean 4.35.0 `Check.lean`, `Compare.lean` and `Axioms.lean` read-only. The ordered export list exactly equals `builtinTargets ++ theorem_names ++ permitted_axioms ++ primitiveTargets ++ definition_names`: 72 entries, including all 26 primitive targets and four quotient builtins. The fixed definitions remain outside the definition-hole list. The three permitted axioms are `propext`, `Quot.sound` and `Classical.choice`. No comparator or kernel was executed to establish these source-level conclusions.

## Independent offline checks

I verified every SUPPORT entry, trusted source/pin hash, frozen preparation gate and prepared input index. Mathematical source/pin files match their baseline Git blobs. The complete current prepared index has 27 entries; the index and runtime preparation receipt are separately bound. Base-stage metadata remains explicitly distinguished from PR27's final Challenge overlay.

I independently executed the Python/Git-only preparer into a new directory and compared every generated file, including receipts, with the author's retained prepared output and repeat generation: byte-identical. I independently reproduced rejection of an existing output directory, a modified mathematical source in an isolated copy, and a changed request in an isolated copy. Drift controls returned nonzero before creating their requested output. The retained local validation's counts, hashes and claimed boundaries agree with these observations. No mathematical source or contribution file was edited for these tests. A corrected reviewer-fixture omission is recorded transparently in the JSON review inputs.

## Handoff and retained-evidence requirements

The repository working tree contains the source, frozen Challenge/config, pin files, preparers, complete export list and required request/return instructions. Publication of the handoff commit remains necessary before a remote clean checkout can reproduce them. The handoff requires operator-protected source/challenge/config and result storage, the pinned exporter and dependency identities, no-network build/export, actual supported bubblewrap grants, before/after input and export hashes, raw NDJSON retained in durable archives, complete logs/argv/exit codes, and every one of the six checker outcomes on the exact retained solution stream.

Supplying both exports bypasses the comparator's build/export step; it does not source-bind the streams. The handoff states that limitation and requires protected build/export records. Existing caches remain trusted inputs with provenance, not a claimed hermetic dependency rebuild. Missing/refusing checkers, changed targets, custom axioms, solution `sorryAx`, missing evidence and failed attempts cannot be relabeled as success. Historical per-root axiom evidence must be explicitly bound if reused rather than represented as fresh output.

Open Math OS must supply its actual supported sandbox command, operational limits and durable job configuration and return failure evidence if unavailable. This repository review does not establish platform compatibility or execute a remote job. All new compilation, comparator, transitive-axiom runtime judgment and six-checker execution are deferred to Open Math OS. Local receipt validation, protected-controller acceptance and upstream merge remain subsequent and separate.

## Disposition

No contribution repair requested. Ready for the bounded Open Math OS handoff after publication of the reviewed support. Exact-source comparison and offline preparation are the evidence delivered here; no stronger assurance is claimed.
