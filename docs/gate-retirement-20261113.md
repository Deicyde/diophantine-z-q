# Review gate retirement, November 13, 2026

Step 1 is prepared on `remove-protocol-d-references`, following the policy changes in `b96f679b`. This is a proposal for the repository owner to merge after changing the ruleset. It does not activate Protocol B or remove the required App check by itself.

## Changes

Six workflows now run only by manual dispatch: `quartic214-manuscript`, `quartic214-manuscript-revision2`, `quartic214-manuscript-revision3`, `quartic214-protocol-d-progress`, `quartic214-research`, and `version16-checks`.

The first three also contain historical manuscript assembly or PDF builds. The research workflow also contains genuine finite computations. They were not classified as exclusively review-record checks. The 214-variable builder, exact coefficient checker and numerical certificate are now in an automatic Research checks job. The current manuscript still builds through `scripts/build_paper.py` and `docs/current-manuscript.json`.

Thirteen distinct review-record, theorem-application or historical manuscript-binding commands moved from Research checks into `archived-review-checks.yml`, which is manual-only. Repeated invocations were consolidated there. The finite replays, valuation regression, construction regeneration, publication-version tests and Lean helper build remain automatic.

`kernel-lean.yml`, `version15-current.yml`, and `manuscript-integration.yml` are unchanged. The current TeX, PDF and manuscript selector are unchanged.

Six entries for shared files were removed from `SHA256SUMS`. Four corresponding pins were removed from the Version 17 historical-continuation record. That pin removal is the only committed change under `research/`; no file under `docs/manuscript-revisions/` was changed. Existing review decisions and surviving digests were not refreshed.

## Proposed required checks

Retain the following existing Research checks, whose historical display names are unchanged:

- `Accepted Lean helpers and axiom audit`
- `Construction regeneration and finite checks`
- `Paper build`
- `Reconstructed quartic and Version 5 inventory`
- `Version 6 quartic reproduction and inventory`
- `Version 9 odd-product replay`, for both existing operating systems
- `Version 12 source and quartic replay`, for both existing operating systems
- `Version 13 source and quartic replay`, for both existing operating systems

Also require `Current 214-variable quartic and numerical certificate`, retain `Complete kernel build and exact-target audit`, and retain the existing current-quartic verification job `current-222` as a required computation check. This makes 14 check contexts including the operating-system variants. Remove the required `Protocol / independent agent audit` App check when merging this retirement. None of the manual archive workflows should be required.

The display names containing "inventory" are historical names; their standalone application-inventory commands have moved to the manual archive workflow. A green computation check does not establish mathematical correctness.

## Local measurements

These are actual command wall times from a clean checkout of commit `2f30dcd90167432c3f8fcea4fec3319aef87555d`, on Windows with Python 3.14.7 and Node 24.22.1. They are not measurements of GitHub queue time, setup, or the Ubuntu/Python 3.12 jobs. The helper build uses Lean 4.35.0 and read-only dependency artifacts at checked source revisions. The paper build uses pinned Tectonic 0.17.0 and its pinned TeX bundle.

| Command or check | Seconds | Outcome |
|---|---:|---|
| 214-variable builder | 0.164 | Passed |
| 214-variable exact checker | 0.406 | Passed |
| Numerical certificate and negative controls | 0.207 | Passed |
| Version 13 portability tests | 4.009 | Passed |
| 394-variable replay | 12.825 | Passed |
| 299/314-variable source lineage | 27.302 | Passed |
| 498/514-variable replay | 12.188 | Passed |
| Odd-product replay | 16.620 | Passed |
| Valuation regression | 0.091 | Passed |
| 962-variable replay | 7.121 | Passed |
| 1,272-variable replay | 20.891 | Passed |
| Original construction regeneration and finite checks | 9.878 | Passed |
| Terminal-row serialization check | 0.221 | Passed |
| Lean helper source checks | 0.313 | Passed |
| Publication-version tests | 18.378 | Passed |
| Current-manuscript tests | 1.086 | Passed |
| Current TeX/PDF pair validation | 0.211 | Passed |
| Publication transition against merged Version 17 | 3.181 | Passed locally; not a hosted event decision |
| Existing 222-variable verifier | 2.209 | Passed |
| Current Version 17 manuscript build | 92.189 | Passed; no TeX errors or unresolved references |
| Fresh 48-helper Lean build and axiom audit | 495.203 | Passed; 704 declarations checked |
| Full kernel build and exact-target audit | 1,702 on GitHub | Separate unchanged hosted retry passed; not a local measurement |

The 214-variable scripts write platform-native newlines. Their five generated JSON files had identical parsed contents, and differed only by CRLF versus LF on this Windows host. The original bytes were restored after recording that comparison. The Ubuntu-only clean-tree assertion has not been reproduced locally. No compatibility wrapper or new normalization was added. The local WSL installation has only Docker Desktop, not a general Linux distribution for this check.

The rebuilt PDF is not byte-identical to the published PDF. This build did not replace it or claim semantic PDF identity. The source, published pair and their declared mapping passed the existing checks.

## Remaining limitations

The 962-variable replayer still inspects stored source-equivalence receipts within its frozen package as part of the same program that reproduces coefficients. It passed locally. Separating that internal operation would require editing the historical checker; this workflow change leaves it intact and does not claim every historical binding has been removed.

Removing shared-file pins intentionally does not renew the old Version 17 continuation acceptance. Its old checker requires the original record and its self-bindings, so it is not expected to pass on the edited record. The original evidence remains available at its original commit. Other archived checks may likewise reject later policy changes. Manual retention is not a promise that historical reviews remain current.

No hosted workflow was dispatched for this retirement branch's measurements. The separate [unchanged kernel retry](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43480881477/attempts/2) passed on the merged Version 17 source. Its job ran from 19:27:05 to 19:55:27 UTC. The cause of the earlier runner communication failure remains undetermined.

The ruleset and controller have not been changed. After the owner merges, the next authorized step is to shut down the old scheduled controller and local runner, verify that no process keeps advancing protocol state, and report that the controller repository can be archived. The new Protocol B gate waits for the owner's model-family choices and API secrets. Removal of evidence trees waits for confirmation that their distillation is complete.
