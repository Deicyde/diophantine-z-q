# Archive batch 3: workspace-alias resolution

This index corrects the dependency accounting for PR102. The initial batch description counted repository paths and relative paths but missed original workspace aliases retained in historical manifests. Those references exist; the claim that only the Version17 source-tree manifest referred to the removed files was too strong.

All targets below are preserved at `review-archive-v17`, commit `005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f`. The canonical resolution of each target is `https://github.com/elliotglazer/diophantine-z-q/blob/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/` followed by its repository path below. Its recorded SHA256 was checked against the original file. Historical manifests, verdicts and hashes are unchanged.

An alias resolves only together with the SHA256 recorded beside it in the referring record. Paths were reused across historical versions: a same-named current file may have different bytes and is not then the referenced object. For a listed target under `research/version14/evidence/release-completion-019/`, the original alias `work/source-risk-review-20261107/` followed by the same suffix, together with that target's SHA256, resolves to its archived bytes. Other observed alias/hash pairs are listed below. This does not claim that every file in an old external workspace was committed. A bare SHA256 equal to a target hash likewise identifies the archived bytes; if several target paths share a hash, they are identical-byte copies and the original path determines the directory context for replay. A still-present repository path need not be redirected when it already has the recorded hash.

The matching-record list was obtained by searching the tracked archive files for these 34 target hashes, including bare-hash values, and their known original workspace aliases. It supplements the earlier repository-path scan. A match is not necessarily a broken path: some records refer to an identical-byte copy still present in the current checkout. This is a targeted check, not a claim to discover arbitrary dynamically constructed paths. None of the target files was read by the traced current computation checks or the additional audit-history self-test. Required checks still run on the deletion revision; that is separate from the historical reference accounting.

Historical packet, installation and report-replay commands that need these payloads must use the complete archive checkout. Their invocation against the incomplete current checkout is retired for these records. For example, use `git worktree add --detach ../diophantine-review-archive 005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f` and follow the original tool instructions there. Old external workspace requirements may remain. No current computation check, kernel check or manuscript build is retired, and no script or released manuscript is changed.

## Targets

- T01: `research/version14/evidence/release-completion-019/v14-current-inventory-transport-review-gi-001/REVIEW.json`; SHA256 `b2c5bc063d75ee6b0646183b55acd3a611234cd84ac033a131eb62d8e0a77886`.
- T02: `research/version14/evidence/release-completion-019/v14-disjoint-source-coverage-001/FINAL-COVERAGE-MANIFEST-004.json`; SHA256 `b15460c697a627ce8c6d8069d2eb1270a4fad09d9acb09facc49325ff10cb417`.
- T03: `research/version14/evidence/release-completion-019/v14-disjoint-source-coverage-001/FINAL-COVERAGE-MANIFEST-005.json`; SHA256 `238c5ef0d08b98de18510a3707dc2a38c73058bdf50fce3b9c7695598b8e2688`.
- T04: `research/version14/evidence/release-completion-019/v14-disjoint-source-coverage-001/FINAL-PROTOCOL14-REVIEW-003.json`; SHA256 `b5ca796417e18f65eca0cbbd0d4daa7f3650c635ca4a7cfb8677ae5908ac5788`.
- T05: `research/version14/evidence/release-completion-019/v14-disjoint-source-coverage-001/FINAL-PROTOCOL14-REVIEW-004.json`; SHA256 `6d4f4215251f57b95003c207a26b61f27d961158ab70c5a0aea55eda808d5bda`.
- T06: `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/PER-REQUIREMENT-DISPOSITIONS.json`; SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526`.
- T07: `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/SCHEMA006-REVIEW.json`; SHA256 `c170fca5e48dc64cd1b34f89f2c101679071007b40e7e1d4557a63e446c62eee`.
- T08: `research/version14/evidence/release-completion-019/v14-installable008-structural-review-gi-001/CHECKS.json`; SHA256 `5439a84d27eea25b0e629c6a53d853a6bd0681d4e3412df4fb516430556c04ff`.
- T09: `research/version14/evidence/release-completion-019/v14-installable008-structural-review-gi-001/REVIEW.json`; SHA256 `008d0115a1371500fc98349beee0f707fe354a1d54f6c97cc48cbf8915732b95`.
- T10: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/current-binding-002/ORDINARY-APPLICATIONS.json`; SHA256 `2006c99c95d966435bf629f1588db0f9938313ad61f0a3c96fec1c3f16f8727d`.
- T11: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/current-binding-002/PACKET-CANDIDATE.json`; SHA256 `d0954a02ee2604eae2287c57e92f2769435718e0f4611ef479ea6bee7939f265`.
- T12: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/overlay/docs/manuscript-revisions/version14/final-coverage/CONNECTIONS.json`; SHA256 `96d1772732338e07572f02d27a160c1a69ebd2efc2a03ce028eb76e575041ca9`.
- T13: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/overlay/docs/manuscript-revisions/version14/final-coverage/DOSSIER.json`; SHA256 `29930de636cef87e8455317aebd2a477831a1b6ad77787505803552853debc60`.
- T14: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/overlay/docs/manuscript-revisions/version14/final-coverage/STRUCTURAL-HISTORY.json`; SHA256 `315cd112fcace604ad1ffab86940be48b0e17cd630a75228d9dfc7625d6ac78b`.
- T15: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/INSTALLATION-PLAN.json`; SHA256 `ca775ae91eedd66b3755f67129afc2e58c1ff9cf289c5a2a13abbbb4f2c8ef08`.
- T16: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/overlay/docs/manuscript-revisions/version14/final-coverage/CONNECTIONS.json`; SHA256 `0db0cb6dbbadd7a34babb8620798c0152459d9e29925ff1b155d675d2f018c4e`.
- T17: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/overlay/docs/manuscript-revisions/version14/final-coverage/DOSSIER.json`; SHA256 `84b8c62728f9322c482bfa9f21fa6d31955b8a4edb3b692fb00a52bed2caba8e`.
- T18: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/ordinary-nested-inventory-013/AFTER.json`; SHA256 `0337bec78e4a40644541ca41c15bbb94ba04eb5516ed9b5ba52939224c15ba05`.
- T19: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/ordinary-nested-inventory-013/BEFORE.json`; SHA256 `8909bd47c9bf515ef710b06ab1498673026c2d4dfdb158b368aec6683f910dcb`.
- T20: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/CONNECTIONS.json`; SHA256 `7cf97b4a34f8c644249566a8540f2838be3c7d610b8e9a272433d74a7eed2fe6`.
- T21: `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json`; SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526`.
- T22: `research/version14/evidence/release-completion-019/v14-inventory-dependent-transport-review-gi-001/REVIEW.json`; SHA256 `392cb0179ddae22aac68b870781faf49a5fc515b53b170bdc3fb44b10c786a6d`.
- T23: `research/version15/evidence/222-sourcefirst/final-006/CONNECTION-REVIEW-SUPPORT.json`; SHA256 `770702f3e543cf69fee708a0656afa8ec59e0a329729a859448304a307019c72`.
- T24: `research/version15/evidence/222-sourcefirst/final-006/MANIFEST.json`; SHA256 `130fa20ff584828b42b925605081739f5c4ef3fdc18a4920acff26db61778d9c`.
- T25: `research/version15/evidence/readiness-001/v15-controller-integration-author-001/MANIFEST.json`; SHA256 `c1665c1ab5baba295533f1c78e976189b4df714e782e1a5ff8b69534dd5acc92`.
- T26: `research/version15/history/pre-222-release/ARTIFACT-INDEX.md`; SHA256 `6f68fa4731afa3c52f4e3d1089015319955468c5a457eabe9c2b8436b8892f4d`.
- T27: `research/version15/history/pre-222-release/CUMULATIVE-HANDOFF.md`; SHA256 `5afdd9d9ccc1a4671f6ab9bc9ba776ed529f3f70d627fe0ddd7e6cdb272056f6`.
- T28: `research/version15/history/pre-222-release/README.md`; SHA256 `0530f305265d84159a48a6ad1b81a0c65299f197186346e1c59eb60240bd0d40`.
- T29: `research/version15/history/protocol-candidate-005/ALL-APPLICATIONS.proposed.json`; SHA256 `ac6b2078fe495d4e4d50b52261500b0432113246c85bac4d1a74d3b8d8cb6922`.
- T30: `research/version15/history/protocol-candidate-005/AUTHOR-MANIFEST.json`; SHA256 `1963ff053b0e4e3dd4da6c6a1148c0e3d16ac7746eb5c57cd85e13c104f84931`.
- T31: `research/version15/history/protocol-candidate-005/CONNECTIONS.json`; SHA256 `e3a61b3847fcb65ed625a7a0a5bc0b12980ac23a7ead6b035716e8390a43f1a2`.
- T32: `research/version15/history/protocol-candidate-005/CURRENT-APPLICATIONS.proposed.json`; SHA256 `35cd636958b0afb1a8bd77dc57b81c8f851c2570b761cce1de08f9dba29a086b`.
- T33: `research/version15/history/protocol-candidate-005/DOSSIER.json`; SHA256 `94a1e8dc716eee864072c1730ece01532422cf36d3492b404c86d40b43c446c3`.
- T34: `research/version15/history/protocol-candidate-005/TRANSPORT.json`; SHA256 `85d090f1b57eef53ca861ab13d916a5b2d7d492d3f03d3b273d894527bed8786`.

## Additional recorded alias/hash pairs

- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-disjoint-source-coverage-001/FINAL-COVERAGE-MANIFEST-004.json` with SHA256 `b15460c697a627ce8c6d8069d2eb1270a4fad09d9acb09facc49325ff10cb417` resolves to T02.
- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-disjoint-source-coverage-001/FINAL-COVERAGE-MANIFEST-005.json` with SHA256 `238c5ef0d08b98de18510a3707dc2a38c73058bdf50fce3b9c7695598b8e2688` resolves to T03.
- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-disjoint-source-coverage-001/FINAL-PROTOCOL14-REVIEW-003.json` with SHA256 `b5ca796417e18f65eca0cbbd0d4daa7f3650c635ca4a7cfb8677ae5908ac5788` resolves to T04.
- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-disjoint-source-coverage-001/FINAL-PROTOCOL14-REVIEW-004.json` with SHA256 `6d4f4215251f57b95003c207a26b61f27d961158ab70c5a0aea55eda808d5bda` resolves to T05.
- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-final-composite-review-001/current136-reconstruction/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `docs/manuscript-revisions/version14/final-coverage/prior-own749/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-008/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T06.
- `docs/manuscript-revisions/version14/final-coverage/CONNECTIONS.json` with SHA256 `96d1772732338e07572f02d27a160c1a69ebd2efc2a03ce028eb76e575041ca9` resolves to T12.
- `docs/manuscript-revisions/version14/final-coverage/DOSSIER.json` with SHA256 `29930de636cef87e8455317aebd2a477831a1b6ad77787505803552853debc60` resolves to T13.
- `docs/manuscript-revisions/version14/final-coverage/STRUCTURAL-HISTORY.json` with SHA256 `315cd112fcace604ad1ffab86940be48b0e17cd630a75228d9dfc7625d6ac78b` resolves to T14.
- `overlay/docs/manuscript-revisions/version14/final-coverage/STRUCTURAL-HISTORY.json` with SHA256 `315cd112fcace604ad1ffab86940be48b0e17cd630a75228d9dfc7625d6ac78b` resolves to T14.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/overlay/docs/manuscript-revisions/version14/final-coverage/STRUCTURAL-HISTORY.json` with SHA256 `315cd112fcace604ad1ffab86940be48b0e17cd630a75228d9dfc7625d6ac78b` resolves to T14.
- `docs/manuscript-revisions/version14/final-coverage/CONNECTIONS.json` with SHA256 `0db0cb6dbbadd7a34babb8620798c0152459d9e29925ff1b155d675d2f018c4e` resolves to T16.
- `overlay/docs/manuscript-revisions/version14/final-coverage/CONNECTIONS.json` with SHA256 `0db0cb6dbbadd7a34babb8620798c0152459d9e29925ff1b155d675d2f018c4e` resolves to T16.
- `docs/manuscript-revisions/version14/final-coverage/DOSSIER.json` with SHA256 `84b8c62728f9322c482bfa9f21fa6d31955b8a4edb3b692fb00a52bed2caba8e` resolves to T17.
- `overlay/docs/manuscript-revisions/version14/final-coverage/DOSSIER.json` with SHA256 `84b8c62728f9322c482bfa9f21fa6d31955b8a4edb3b692fb00a52bed2caba8e` resolves to T17.
- `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/source-risk-review-20261107/v14-final-composite-review-001/current136-reconstruction/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `docs/manuscript-revisions/version14/final-coverage/prior-own749/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `work/source-risk-review-20261107/v14-final-composite-review-001/current136-reconstruction/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-008/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `work/source-risk-review-20261107/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/overlay/docs/manuscript-revisions/version14/final-coverage/PER-REQUIREMENT-DISPOSITIONS.json` with SHA256 `6f1347f5d750cfdb737bc9368a5c08ce774cb4ae0f19e380a2fe5fc313c4d526` resolves to T21.
- `work/v15-222-sourcefirst-review-001/final-006/MANIFEST.json` with SHA256 `130fa20ff584828b42b925605081739f5c4ef3fdc18a4920acff26db61778d9c` resolves to T24.
- `work/v15-controller-integration-author-001/MANIFEST.json` with SHA256 `c1665c1ab5baba295533f1c78e976189b4df714e782e1a5ff8b69534dd5acc92` resolves to T25.
- `work/v15-222-serialization-author-001/assembled-preflight-005/MANIFEST.json` with SHA256 `1963ff053b0e4e3dd4da6c6a1148c0e3d16ac7746eb5c57cd85e13c104f84931` resolves to T30.
- `research/version15/protocol/current222/CONNECTIONS.json` with SHA256 `e3a61b3847fcb65ed625a7a0a5bc0b12980ac23a7ead6b035716e8390a43f1a2` resolves to T31.
- `research/version15/protocol/current222/DOSSIER.json` with SHA256 `94a1e8dc716eee864072c1730ece01532422cf36d3492b404c86d40b43c446c3` resolves to T33.

## Matching retained historical records

These files remain unchanged. The identifiers list target hashes or recorded paths matched in them, including bare-hash fields; they do not renew historical approvals or imply that every match is a broken current path.

- `docs/manuscript-revisions/version14/final-coverage/STRUCTURAL-HISTORY.json`: T09.
- `docs/manuscript-revisions/version14/final5882-inventory-transport/REVIEW.md`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-CI-BUILD-RENDER-AND-RETRY.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-CURRENT-REVIEW-RECORD-DISTRIBUTION.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-DOCUMENTATION-AND-NAVIGATION.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-FINITE-ARTIFACTS-AND-VALIDATORS.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-PDF-AND-ANNEX-DELIVERY.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-PROTECTED-CI-POLICY-WRAPPER.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-PROTECTED-HISTORY-POLICY-WRAPPER.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-PROTECTED-RECORDS-POLICY-WRAPPER.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-PUBLIC-POLICY-AND-CONTRIBUTOR-RULES.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-001/bodies/RELEASE-RETAINED-SOURCE-AND-HISTORY-DISTRIBUTION.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-002/REVIEW.json`: T03, T05, T06, T21.
- `research/version14/evidence/release-completion-019/v14-application-report-bodies-arithmetic-002/bodies/RELEASE-CURRENT-REVIEW-RECORD-DISTRIBUTION.json`: T01, T03, T05, T06, T21, T22.
- `research/version14/evidence/release-completion-019/v14-current-inventory-transport-installation-root-001/INSTALLATION.json`: T01.
- `research/version14/evidence/release-completion-019/v14-current-reconstruction-installation-root-001/INSTALLATION.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/COMPLETION.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/OWN-CURRENT007-REVIEW.json`: T07.
- `research/version14/evidence/release-completion-019/v14-final-composite-review-001/current136-reconstruction/USE-RECONCILIATION-REVIEW.json`: T06.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/EXTERNAL015-ACKNOWLEDGMENT.json`: T16, T17.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/protocol14-assembly-023-001/ASSEMBLY-PROTOCOL14-REVIEW.json`: T04.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/protocol14-assembly-023-001/ASSEMBLY-SUPPORT.json`: T02, T04.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/protocol14-assembly-024-001/ASSEMBLY-PROTOCOL14-REVIEW.json`: T05.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/protocol14-assembly-024-001/ASSEMBLY-SUPPORT.json`: T03, T05.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/source-report-bodies-001/FINDINGS65-REPORT.json`: T16.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/source-report-bodies-001/MAIN-APPLICATION-REPORT.json`: T16.
- `research/version14/evidence/release-completion-019/v14-final-disjoint-assembly-review-001/source-report-bodies-001/SCOPED-ASSEMBLY-REPORT.json`: T16.
- `research/version14/evidence/release-completion-019/v14-guide-count-pin-transport-001/APPLICATIONS.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-historical-protocol-findings-review-arithmetic-001/REVIEW-002.json`: T07.
- `research/version14/evidence/release-completion-019/v14-installable010-composition-review-gi-002/CHECKS.json`: T09, T12, T13, T14.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/current-binding-002/MANIFEST.json`: T10, T11.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/historical-intake-accounting-011/ACCOUNTING.json`: T07.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-008/REVIEW-SNAPSHOT.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/INSTALLATION-PLAN.json`: T06, T12, T13, T14, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/MANIFEST.json`: T06, T12, T13, T14, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/PACKET-CANDIDATE.json`: T12, T13, T14.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-010/SELECTED-INPUTS.json`: T09.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/MANIFEST.json`: T06, T14, T15, T16, T17, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-012/PACKET-CANDIDATE.json`: T06, T14, T16, T17, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-024/ACCEPTED-REVIEWS.json`: T03, T05.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-024/INSTALLATION-PLAN.json`: T06, T14, T16, T17, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-024/MANIFEST.json`: T03, T05, T06, T14, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/installable-024/PACKET-CANDIDATE.json`: T06, T14, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/merged-incoming-021/DOSSIER-PRE-HISTORY.json`: T16.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/ordinary-nested-inventory-013/MANIFEST.json`: T01, T18, T19.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/BINDINGS.json`: T06, T07, T21.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/MANIFEST.json`: T20.
- `research/version14/evidence/release-completion-019/v14-integration-source-line-index-work-001/final-protocol-preparation/own-current-007/OVERLAY-MANIFEST.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-inventory-contract-renewal-arithmetic-001/overlay/docs/manuscript-revisions/version14/final5882-inventory-transport/REVIEW.md`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-inventory-dependent-transport-author-002/INPUTS.json`: T01.
- `research/version14/evidence/release-completion-019/v14-inventory-final-bindings-author-002/CURRENT-BYTE-DELTA.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-inventory-final-bindings-author-002/INPUTS.json`: T22.
- `research/version14/evidence/release-completion-019/v14-inventory-final-bindings-author-002/classification/APPLICATIONS-DRAFT.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-inventory-final-bindings-author-002/classification/CLASSIFICATION.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-inventory-final-bindings-author-002/classification/FILE-INVENTORY.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-ordinary-nested-inventory-review-arithmetic-001/REVIEW.json`: T01, T18, T19.
- `research/version14/evidence/release-completion-019/v14-ordinary176-review-arithmetic-003/REVIEW.json`: T01.
- `research/version14/evidence/release-completion-019/v14-release-final-pin-correction-002/APPLICATIONS.json`: T06, T21.
- `research/version14/evidence/release-completion-019/v14-release10-review-arithmetic-002/DECISIONS.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-release10-review-arithmetic-002/REVIEW.json`: T01, T22.
- `research/version14/evidence/release-completion-019/v14-union012-installation-root-001/INSTALLATION.json`: T06, T14, T16, T17, T21.
- `research/version15/evidence/222-normalization/v15-222-serialization-review-arithmetic-005/REVIEW.json`: T30.
- `research/version15/evidence/222-release-infrastructure/integration-checks.json`: T25.
- `research/version15/evidence/222-sourcefirst/final-006-target-supplement/ALLOCATED-TARGET-SELECTION.json`: T24.
- `research/version15/evidence/222-sourcefirst/final-006-target-supplement/MANIFEST.json`: T24.
- `research/version15/evidence/readiness-001/v15-controller-integration-review-h6-001/REVIEW.json`: T25.
- `research/version15/evidence/readiness-001/v15-namespace-preparation-author-001/CUTOVER-INPUTS.pending.json`: T25.
- `research/version15/history/protocol-candidate-005/COVERAGE-APPLICATION.proposed.json`: T31, T33.
- `research/version15/protocol/current222/AUTHOR-MANIFEST.json`: T30.
- `research/version17/MANIFEST.json`: T01, T02, T03, T04, T05, T06, T07, T08, T09, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28, T29, T30, T31, T32, T33, T34.
