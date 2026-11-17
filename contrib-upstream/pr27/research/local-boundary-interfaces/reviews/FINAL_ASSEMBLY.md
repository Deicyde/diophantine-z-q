# Final assembly review

Date: 2026-11-10. Reviewer: Codex `/root/normalization_claim_review`.
This is a separate supplement to the preserved core proof/control review.
The reviewer did not author the four modules, runners, application note,
clean-run wrapper or final status documents. The same model environment,
host and dependency caches permit correlated errors; this is not external
human acceptance or an independent proof-checker result.

**Decision: PASS for the bounded local preparation and its stated development
assurance profile.** The additional clean-project-reproduction gate is met
under the disclosed dependency-cache trust. No mathematical source, application
or checking-code change was required by this final review. Publication and
hosted acceptance remain separate.

## Preserved core and current input identity

The frozen preparation snapshot is
`0715d6bf23d63e552c68a1dced24a85d216fa9b7`. I checked all 22 input hashes in
`PROOF_REVIEW_INPUTS.json` against that Git snapshot. Its 28 bound evidence
files, the core report and the control review remain unchanged. The only
previously reviewed input documents changed since that snapshot are
`VERIFICATION.md`, `FINDINGS.md` and `PR_DESCRIPTION.md`, which now report the
completed clean run and the comparison correction. I read their complete
current text and inspected their differences. The last additional edit only
normalized three assurance-status cells to `PASS`; their scope descriptions
were unchanged.

The four mathematical source files, README, APPLICATION, TARGETS, ORIGIN,
dependency pins, native runner, control script and test design are identical
to the core-reviewed inputs. The previous review therefore remains a truthful
record of the pre-clean stage; it has not been rewritten to claim a check
that had not yet occurred. This supplement binds the new evidence and current
status text instead.

## Clean reproduction inspection

I read the complete `evidence/clean/REPRODUCTION.json`, comparison note and
retained stdout/stderr, and independently inspected the clean worktree.
Its HEAD is the displayed frozen commit, detached, and its current Git status
is empty. The receipt records a clean tracked tree before and after execution
and no preexisting project output. I did not witness the historical before
state directly or launch another Lean run for this supplement.

All three recorded commands returned zero: the selected native runner,
finite controls and existing protocol self-test. Their retained stream hashes
match the actual files. I compared all 17 native receipt files in the clean
worktree with the published `evidence/native` files; every byte agrees. The
four newly compiled `.olean` hashes agree with the first run. The 12 native
input hashes agree in the clean checkout, current submission and receipt.
This includes the reviewed source/application/runner bytes; it is not merely
a comparison of successful exit labels.

The complete clean control output is byte-identical to this reviewer's earlier
Python 3.13.12 reproduction. Comparing it with the author's output gives
exactly one JSON difference: Python 3.12.3 versus 3.13.12. Every other field,
including input hashes, counts, witnesses and mathematical results, agrees.
The protocol stdout is also byte-identical to the first retained output.

The initial postprocessing wrapper did fail an overstrict author-output byte
comparison. Its preserved stdout records `native 0`, `controls 0`, `protocol 0`
before the retained `AssertionError`. The final receipt and note disclose the
failure and its correction. The exact comparisons above support the stated
resolution; no proof/control source, mathematical tolerance or output bytes
were changed to make a failing mathematical case pass.

This is a fresh project checkout and output directory on the same host using
the same pinned dependency caches. It is neither a dependency source rebuild
nor a hermetic or independent-host execution. Native kernel checking of the
fresh selected modules and transitive axiom collection retain the trust limits
already stated in the core review. No paranoid run, external kernel checker,
export replay or frozen-statement protected comparison is added here.

## Preservation, manifest and claims

I read `evidence/PRESERVATION.json` and independently checked all 3,175 tracked
research-checkout file hashes against the retained intake snapshot; all agree.
The research checkout remains at
`33483f751e6dcd3f91fb303969838aca33ad0458`. The tracked candidate diff against
the V13 base contains additions only. The foundation PR's remote state in the
preservation receipt is the integrator's dated observation; this reviewer did
not query the remote service again.

I independently hashed every one of the 62 entries in `MANIFEST.sha256`, checked
for duplicate paths and verified that its inventory is exactly the four source
modules plus packet files, except the declared exclusions. The final manifest
SHA-256 is
`ce59e6667e58c1858a0bb87830c35f4142dc1f69c805f2e4daaa169f130220e3`.
It excludes itself and the two final assembly attestation files to avoid a
hash cycle. `FINAL_ASSEMBLY_INPUTS.json` binds this report, that manifest and
the observed hashes of all 62 covered files. The ensuing Git snapshot can
bind those attestation files without self-reference; this review does not
invent a future commit identity.

Current verification and proposed PR language accurately distinguish the
completed local package from unperformed hosted checks, maintainer acceptance,
and the wider arithmetic programme. The frozen 39-target foundation's cloud
evidence is not attributed to these 41 selected proof roots. The four-module
contribution remains conditional local conjugation, cup correction and
comparison preservation under explicit hypotheses. This assembly review does
not establish the actual global arithmetic cup/trace instance, every required
inverse, stored-functional identification, integral determinant normalization,
retained-limit descent or the main Diophantine theorem.

No further local mathematical or packaging defect was found in the bound
payload. This decision authorizes no push, PR creation, merge or change to
historical/core evidence; it records the reviewed local result only.
