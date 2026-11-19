# Version 21 draft: tables and build review (Fable, 19 November 2026)

Local review of Astra's uncommitted Version 21 candidate at
`C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\version21-explicit229-20261118\repo`
(HEAD b013ec53, equal to origin/main, plus working-tree changes). Not a gate result. Nothing was posted, pushed or written to the relay, and nothing in the worktree was modified.

**Result.** No error found in build selection, source/PDF/build correspondence, preservation of released files, or the printed tables. A builder record is prepared at `C:\Users\glaze\Documents\fable-v21-builder-review-draft.json` with decision `accepted_within_scope`. Five housekeeping points should be settled before the pull request (see Notes). The new arithmetic of Part I was not reviewed here.

## Hashes

All three match Astra's request.

| File | SHA-256 | Bytes |
| --- | --- | --- |
| `manuscripts/quartic_v21.tex` | f72580eaeaea95933fcd9d631d6f8577586543117ad10124abf4fe346befee07 | 2,862,137 |
| `manuscripts/quartic_v21.pdf` | 9d61d436ade520621ec8730cf39566ca03895bdafce671d4b3440afa6a9ae5bd | 5,400,822 |
| `research/version21/BUILD.json` | f47808193c55911497abd44cddeb63b844aa03b98fa789b6e8aed3a19b000940 | 221,420 |
| `docs/current-manuscript.json` | f3c2d36b3a3daf54e8a03d6c1e4f54db634f178e27e1b6d16fd802c47dc973af | 534 |

## 1. Build selection and correspondence: holds

- `docs/current-manuscript.json` declares version 21 with the three hashes above; `scripts/check_current_manuscript.py` exits 0.
- `BUILD.json`: manuscript_version 21, status success, source and PDF hashes equal to the files, builder hash 5afbf705… equal to `research/version18/build_pdf.py`, three serial passes each with return code 0, tex_errors 0, unresolved_references 0, 832 pages.
- `scripts/build_paper.py`, `scripts/check_current_manuscript.py` and `research/version18/build_pdf.py` are unmodified from origin/main and are the same bytes as in my Version 20 record.
- PDF (pdfinfo, pdftotext): 832 pages; title "Z is Diophantine in Q, Version 21"; no "??"; no draft wording on the first pages. The abstract gives 229 variables, 3 312 monomials, 149^30 < 2^217, 74 007 bytes, and 195 variables with 2 956 monomials. The AI usage statement is word for word Version 20's.

## 2. Released files preserved: holds

- The ten files `quartic_v16` to `quartic_v20` (.tex and .pdf) hash to their Git blobs at HEAD and origin/main, to the values in my Version 20 record (v16 to v19) and to the Version 20 release values (TeX 95044840…, PDF 061c4353…).
- Changed relative to origin/main: `CREDITS.md`, `README.md`, `THIRD_PARTY_NOTICES.md`, `docs/current-manuscript-build.md`, `docs/current-manuscript.json`. Added: the two Version 21 manuscript files and 30 files under `research/version21/`.
- Nothing under `.github/`, `scripts/`, `tests/`, `releases/`, `KERNEL_CONTRACT.json`, any earlier `research/versionK/`, or `research/brox-explicit229-v68/`. Every added data file has an extension the scope rule exempts under `research/versionNN/`, so the version pull request should need no kernel build.
- README: the contributor line is untouched and includes Jennifer Park.

## 3. Printed tables: all checks pass

My own parser and scripts (scratchpad `v21/v21tables.py`, `v21/copymaps.py`, `v21/m6det.py`), reading the TeX and Jose's data files at main b013ec53. None of Jose's programs was executed.

- 207 printed source rows equal `source/quadratic229-v62.json`; 207 printed normalized rows equal `quadratic.json`; the printed exponent lists (229 and 207 entries, a_1 = 0) equal `transformation.json`.
- R_j = 149^{b_j} Q_j(149^15; 149^{a_i} y_i) reproduces every printed normalized row from the printed source rows. Every normalized row is integral and primitive.
- Expansion: exactly coordinates 1 to 229, 3,312 monomials, degree 4, content 1, coefficient of y_1^4 equal to 1, largest coefficient exactly 149^30 (217 bits), attained at y_77^2 y_101^2, y_104^2 y_112^2 and y_111^2 y_112^2 as the text says.
- Plain notation: 74,007 bytes, SHA-256 45bdea1e…cea1975, byte-identical to `quartic229-N15.txt` and equal to `polynomial.json` on main.
- The stated unnormalized height 149^32 with the same 3,312-monomial support is correct.
- Copy maps: the 34 printed coordinate copies and 31 printed row copies equal `graft.json`; both are injective; each copied source row is the literal renaming of its original.
- Retained body: after normalizing line endings, Version 21 differs from Version 20 in seven hunks only: title, date, PDF title, three abstract lines, the new Part I (3,938 lines), and the two insertions Astra describes (five lines in the 244-coordinate starting system; ten lines giving the determinant of M_6). So the 195, 247 and 250 tables and map sections are line for line Version 20's.
- The inserted determinant: recomputed from the six printed rows, det M_6 = 1/214450708242592116705963714180667354532074632082, and the three 2x2 block determinants and their product are as printed.

## 4. research/version21: consistent

- `construction/INPUTS.json`: all nine files match their recorded hashes and sizes and are byte-identical to the files in `research/brox-explicit229-v68/` on main.
- `RELEASE-MANIFEST.json`: its eight path/hash entries match the files.
- `FINITE-CHECKS.json` records the manuscript hash f72580ea… and the current hashes of the five scripts it lists, each with exit code 0. I ran `verify247_retained.py`, `verify229.py`, `verify_arithmetic.py` and `check_printed.py` individually; each exited 0 with output consistent with the record.
- `CORRECTIONS.json`: 25 items, unique IDs, each with an issue-129 comment link; all class C; 22 marked implemented and 3 deferred (CI registration). Every label (`v21:…`, `v20:…`) and file named in a disposition exists. I did not judge whether each disposition answers its note.

## Notes (none is a defect in the reviewed correspondence)

1. **CRLF line endings.** `quartic_v21.tex`, `BUILD.json` and `docs/current-manuscript.json` use CRLF; every earlier released TeX uses LF. The attributes file stores these paths without conversion, so the recorded hashes bind the CRLF bytes and the commit will carry them. It works, but it is a change of convention, whole-file diffs against Version 20 show every line as changed, and any later normalization invalidates every hash. Decide now whether to keep it; if the TeX is rewritten with LF, the PDF must be rebuilt and all records reissued.
2. **"Current version" text, changing under review.** When I started, `manuscripts/README.md`, `docs/research-guide.md` and `CITATION.bib` named Version 20 as current and there was no `CURRENT_VERSION21.md`. At about 03:13 UTC, while I was reviewing, the worktree changed: `CURRENT_VERSION21.md` appeared and the first two documents were modified. They now say Version 20 is the current *published* manuscript, and `CITATION.bib` still has no Version 21 entry. I rehashed the TeX, PDF, `BUILD.json`, the profile and the builders afterwards; all unchanged, and `check_current_manuscript.py` still exits 0. The path lists in section 2 describe the state before that edit.
3. **"Candidate" wording.** `README.md` says "Version 21 candidate" and "Version 20 remains the published release until this candidate has the required review and release approval", and `RELEASE-MANIFEST.json` has status "Candidate". The gate merges on acceptance, so this text would be on main as the current description after the merge. Either word it for the merged state or plan the follow-up.
4. **Builder binding.** `docs/audit-history/builder-binding.json` still binds Version 20, and `check_audit_history.py --self-test` stops at "Changed bound file: docs/current-manuscript.json". Expected until the binding is updated with a Version 21 record.
5. **AI usage statement and credit.** The statement is unchanged from Version 20 while the new construction is Jose Brox's. The manuscript agent guide asks that it name every agent that contributed to the version; whether agents Jose used should be named needs his answer. His confirmation of the CREDITS line is also a release condition.

## Not checked

- The new arithmetic of Part I: the torsion-inclusive height bound, the cutoff-free extraction, the N = 15 argument, completeness. This needs its own text review.
- `DEPENDENCIES.md`, the substance of the 25 dispositions, the handoff files.
- No build was run and no page images were inspected; the two rewrapped copy tables were checked as data, not visually.
- `research/version21/construction/check.py` and `research/version20/construction/check.py` were not run as wrappers because they write under `build/`.
- Nothing was checked on Linux or in CI.

## Draft relay note to Astra (not sent)

From: Fable. About: Version 21 draft, tables and build review. Needs reply: no.

I checked the exact bytes you named (TeX f72580ea…, PDF 9d61d436…, BUILD.json f4780819…). Build selection, source/PDF/build correspondence and preservation of the ten released files hold, and I can issue the builder record; the prepared record is `C:\Users\glaze\Documents\fable-v21-builder-review-draft.json`. With my own parser, all 207 source rows, all 207 normalized rows, both exponent lists and both copy maps equal Jose's data on main; the expansion gives 229 variables, 3,312 monomials, height 149^30 at the three named monomials, and 74,007 bytes with the stated digest; det M_6 and its three block determinants are as printed; the retained body differs from Version 20 only in the two insertions you list. Full report: `C:\Users\glaze\Documents\fable-review-v21-tables.md`.

Before the pull request, please settle: (1) the TeX, BUILD.json and current-manuscript.json are CRLF where every earlier version is LF; keep or change now, since changing later reissues every hash; (2) manuscripts/README.md, docs/research-guide.md and CITATION.bib still say Version 20 is current, and there is no CURRENT_VERSION21.md; (3) README and the release manifest say "candidate" and will be on main after an automatic merge; (4) the AI usage statement is unchanged; ask Jose which agents, if any, should be named, and for his confirmation of the credit line. I have not reviewed the new arithmetic of Part I; that is a separate read.
