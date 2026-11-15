# Distilled review records for diophantine-z-q

Compiled 2026-11-13 from the repository at commit `8799c581` (current `main`, Version 17). This folder condenses the written review material under `research/` and `docs/` into four documents a reader can use without opening the records themselves.

| File | What it holds |
|---|---|
| [findings-ledger.md](findings-ledger.md) | Part 1: 43 objections from outside the project's agent pool (Fable audits, GitHub issues, experts, collaborators). Part 2: 266 substantive findings extracted from the internal written reviews. |
| [proof-index.md](proof-index.md) | The 81 standalone proof notes in the records, each with its claim and whether its argument appears in the Version 17 manuscript. |
| [source-inventory.md](source-inventory.md) | 104 published sources the proof relies on: version read, statements used, where consumed, recorded qualifications. |
| [review-file-table.md](review-file-table.md) | One row for each of the 413 written reviews and reports: subject, decision, and whether it carries a finding. |

## Headline numbers

**Outside objections (43).** 29 resolved (2 by withdrawal), 8 partly resolved, 5 open, 1 whose resolution could not be located.

**Internal findings (266).**

| Kind | Count |
|---|---:|
| Error in the mathematics or in a cited source | 56 |
| Gap or missing justification | 65 |
| Hypothesis or convention not checked | 51 |
| Overstated claim | 24 |
| Stated limitation of what was reviewed | 70 |

About 57 of these are recorded as open, pending or not accepted by the review that raised them. That count is a text match on the status line, and many may have been closed by later work.

**Standalone proofs (81).**

| Status against Version 17 | Count |
|---|---:|
| Argument found in the manuscript | 46 |
| Statement used, argument not reproduced | 26 |
| Not found by search | 7 |
| Route recorded as superseded | 2 |

## Check these first

These are the items the readers flagged as most likely to matter. **They have since been checked against the manuscript: none is a real gap. See [flagged-items-check.md](flagged-items-check.md).** The original flags are kept below as written.

**Proofs that may not have reached the manuscript**

- `heegner-kernel-specialization-current` and `cj-global-atkin-identification-current`: Version 17 asserts the conclusions (near lines 8989 and 21028). Its only good-model argument (near line 35252) covers isogeny degree prime to qN, which both notes say does not apply.
- `local-twist-factors-002`: "local factor is one at active primes" (near line 18818) rests on an additive-reduction argument that was not found in Version 17.
- `qm-idempotent-image-v1` and `real-kummer-lattice-v1`: results asserted (near lines 13745 and 19402) without the arguments.
- `pan-local-rings-v1`: supplies flatness for Pan's lifting ring and corrects a claim in Pan 4.2.10. A review records the proof as "not yet in the TeX".
- `general-field-tw-v1`: repairs a hypothesis gap in the Khare–Wintenberger and Kisin auxiliary-prime step. Unreviewed, and Version 17 does not mention either source; the route may have been replaced by direct use of Calegari and Pan.
- `yuan-final-source-v1`: Version 17 avoids Yuan's Lemma 2.1 without recording why (a doubted separability step) or checking that Theorem 1.1 does not depend on it.
- `shared314`: its H-depth bootstrap is flagged in the note as new and outside earlier review; Version 17 prints it unflagged (near line 28478).

**Internal findings recorded as open**

- The beta dyadic conductor step cites Milne, *Class Field Theory* V Prop. 3.3, a global statement; the correct local lemma has its proof marked "to be added" in the source.
- `ACTIVE-BETA-LOCAL-NORM` has no eligible published source.
- Baba–Granath: the printed polarization is 6E, not principal; a degree-four adverse finding remains open.
- Existence of the Emerton weak map is unproved in the records, and the Emerton 2011 draft prints det^b where det^(b+1) is needed. This belongs to the CEGGPS route, which Version 17 may no longer use.
- The all-prime irreducibility proof assumed a quadratic field inside B that neither family construction has; the successor's attachment to the b-family awaits review.
- For the 214-variable family (PR 30), the review batch records complete-proof acceptance as "not accepted", with 33 source bindings pending at that time.

**Outside objections still open**

- Unnamed hypotheses in theorem statements, and the abstract's sentence about the constant C.
- Fable's second-pass text corrections.
- Kato 1999 pp. 314–318 and Ribet 1990 pp. 440–443 were not read by any outside auditor, although the p=2 Kato repair rests on them.
- The Baba–Granath ramification and CM-count locator audit.

**Parts of the proof no outside auditor has reviewed**

- Everything after Version 15, including the 214-variable family in Version 17.
- The restricted converse since November 4, apart from changed passages.
- The Tao–Ziegler arguments with the changed modulus.
- The Shimura-curve geometry in the height chain.
- Sections 14–18 and Appendices I–J (skipped by the Issue 2 reviewer), and the Version 11 Kato repair was not rechecked by that reviewer.

**Source inventory gaps**

- No source-use inventory is bound to Version 17; locations come from Version 16 line ranges.
- Sources for the 214-variable family rest on an author record awaiting review.
- Nine works used in the Version 16 dossier are missing from the Version 17 bibliography, and eleven cited works have no dossier record.
- Pan's final JAMS text and Rémond 2022 were never accessed.

## How this was made, and its limits

- Fourteen reader agents (Claude) each read one slice: three for the proof notes, nine for the written reviews, one for the existing source inventories, one for outside audits including nine Fable audit PDFs.
- Byte-identical copies were removed first. Hash strings were stripped from the text the readers saw.
- "In the manuscript" was judged by text search of a 2.3 MB TeX file, not by reading it. "Not found" means the searches failed.
- Statuses are those recorded by the cited file at the time. They were not reconciled across batches or against later records, so some "open" items are closed and the same issue may appear more than once.
- The readers classified findings by judgment; the counts are indicative.
- Not read: the 6,082 JSON records, GitHub issue and pull-request discussions, and the review material outside `REVIEW.md`, `REPORT.md`, `INDEPENDENT-REVIEW.md`, `RUNTIME-REVIEW.md` and `PROOF.md` files.
- Buzzard, Savitt and Pasten are not named in the repository; their objections were matched to records by content.
- Nobody has checked the readers' extractions against the originals. Spot-check before relying on any single entry.
