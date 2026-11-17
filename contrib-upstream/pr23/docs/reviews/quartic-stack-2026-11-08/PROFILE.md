# Scope profile for the conditional research PR stack

Profile date: November 8, 2026. Governing protocol: v1.2 at upstream commit
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. This is an author proposal for
independent assessment, not a final-release acceptance record.

The claimed deliverable is a set of reproducible conditional research
contributions, with explicit local arguments and review evidence. It is not
an integrated new manuscript release or full verification modulo published
theorems. The mathematical packets and their original source hashes remain
unchanged when the upstream policy and this handoff are merged into the stack.

The project publication rule in `docs/release-policy.md` calls for a new
optimization edition after crossing below 300 variables, the next threshold
after Version 13. None of these proposals crosses it. That rule does not
excuse a substantive repair requiring a release, nor does it waive research
handoff duties. These PRs propose conditional alternative constructions and
do not claim to repair or replace the current manuscript's theorem.

| Duty | Applicability and evidence |
| --- | --- |
| Cumulative handoff, retained negative results, provenance | Applies. HANDOFF.md, ARTIFACTS.json and the immutable complete packet manifests retain actual evidence and corrections. |
| Exact artifact specification and hashes | Applies. EVIDENCE_MANIFEST.json covers the listed packet scopes; HANDOFF_MANIFEST.json covers this handoff. Distinguish committed tables from reproducible generated expansions. No archive completeness beyond the declared scopes is asserted. |
| Source/application inventory and findings | Applies. Retain all package inventories, later contracts and received review reports; FINDINGS.json records remaining source integration and coverage work. Full published-source completion is not claimed. |
| README/current-paper links/current TeX/current PDF | No replacement in these non-release contributions. These remain the unchanged Version 13 release surfaces, hashed in EVIDENCE_MANIFEST.json. PR and packet statements consistently call the new work conditional proposals. The complete synchronization duty applies when a new current release is designated. |
| Source-to-PDF release identity and version/date | No new current PDF is issued here. Preserve the original package proposal PDF as historical evidence. Existing release identities are retained; this profile does not retroactively attest a fresh PDF build. |
| Current artifact catalog/theorem inventory/current acceptance register | Preserve existing release records. New research is catalogued here and in its own application inventories. Updating the current theorem or release catalog as though this were already incorporated would overstate the outcome. |
| Citation, credit and dependency change review | Applies. Preserve original citations and attribution byte for byte; record the old-base/Kato comparison and pending current-source integration. Local reductions are attributed and separately reviewed. |
| Link checks and public readback | Applies to the listed immutable evidence and authorized fork/PR destinations. Verify Git blob hashes and public ref/manifest readback; distinguish object-integrity checks from mathematical coverage. |
| Private-mirror synchronization | Not performed: no new official mirrored release is being issued and private publication was not authorized. An eventual release must identify intended differences and verify every configured authorized destination. |
| Independent review and designated App check | Applies. A separate reviewer assesses this scope and unchanged-source comparison. The required App must independently bind its own check to actual base/head/merge revisions. Our reports do not authorize or impersonate it. |

Required source-packet names and locations are the directories in
ARTIFACTS.json. Preserve all their tracked files; do not prune by size or
overwrite earlier editions. Full generated polynomial trees may remain
reproducible outputs, provided their exact expected hashes and commands are
retained and no committed-full-expansion claim is made for them. This
research profile introduces no new official release inclusion threshold.

The public readback and independent scope assessment must be supplied as
separate evidence records and linked at immutable versions from the PRs.
Their completion must be checked against the actual final heads. Their findings
may require amendments to this profile; pending scope or App review must not
be described as full protocol completion. No claim is made that component
reviews alone satisfy the protocol's final assembled-proof closure test.
