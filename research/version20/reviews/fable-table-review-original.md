# Fable check of the Version 20 draft: printed tables, stated numbers, source/PDF/build

17 November 2026. Root: `C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\version20-release-20261117\repo` (branch `codex/version20-247`, HEAD = origin/main = 3d2c9e56, candidate uncommitted).
Source `manuscripts/quartic_v20.tex` SHA-256 `fa1e3eb43be998a157e64883a3ecf6d703cca8790ea1ee5ce8a858b1b4196f37`; PDF `manuscripts/quartic_v20.pdf` SHA-256 `b99d8f0de41986925912b459c97c7fd4dcf9808a7025663f9885b0a7166bd97a`.

Scripts (mine): `v20tables.py`, `v20extra.py` in the session scratchpad. They read the TeX and JSON only. I did not import or run Astra's `check.py`, `check_printed.py`, `verify247.py`, or any of Carbon's or Jose's code. The byte count uses `docs/explicit-record/measure_plain_text.py` from PR 145 (my own file).

**Result: no mismatch found in any item below.**

## 1. The 219 printed rows of the 247

- All 219 `align*` blocks in Section `v20:247-rows` parse; row ids 1..219 present.
- Every printed row equals Carbon's `explicit247-quadratic.json` exactly (same sign, no row differs). The 219 embedded `% V20-ROW` comment rows equal the typeset rows.
- Every row is quadratic, integral and primitive.
- Expansion of the sum of the 219 squares: 247 variables occur, 3,385 monomials, degree 4, coefficient of x1^4 equal to 1, content 1.
- Largest absolute coefficient: attained only at the constant term, equal to 149^10220 + 298442980098761875927809873. That number has bit length 73,780, so it is below 2^73780 (and at least 2^73779). The split stated in the proof holds: the ladder row contributes 149^10220, the other rows' constants contribute 298442980098761875927809873.
- Plain notation (PR 145): 96,712 bytes, SHA-256 `455afb0b7143654119db3a68a85fec2fde566cf7fbdf3f7c84bd5d75b32719b9`. Equal to the committed `research/version20/construction/inputs/carbon/tables/explicit247/quartic247-decimal.txt` (96,712 bytes, same hash).

## 2. Printed scalings, row operations, permutation

- Coordinate scalings table: 65 entries, all nonzero, equal to the certificate's `coord_scales`; lambda_1 = lambda_47 = 1.
- Row multipliers table plus the fifteen displayed combination rows (58, 64, 65, 102, 120, 121, 138, 156, 175, 179-184): the resulting 216 x 216 matrix T equals the certificate's `T_rows` entry for entry. No row is in both lists.
- T times the certificate's inverse is the identity (exact). det T is nonzero and equals the certificate's `det_T`.
- det M_6 (indices 179..184) = 1/214450708242592116705963714180667354532074632082, as printed. The 121/175 block is ((2,2),(-1,3)) with determinant 8, as printed.
- Off-block entries are (58,112), (64,10), (65,11), (102,108), (120,126), (121,216), (138,144), (156,162); they are acyclic between blocks and every other diagonal entry is nonzero, so the block-triangular remark in the text is right.
- Permutation table: 8 and 90 distinct old indices, none of 1, 245, 246, 247; the prescription is a permutation of 1..247; it equals the certificate tiers and the coordinate map in Carbon's table.
- Applying the printed scalings, the printed T, A -> z_247 and the printed permutation to the Version 19 unbalanced 244 rows (`unbalanced244-quadratic.json`, SHA-256 dad70be3...) reproduces printed rows 1..216 exactly: 216 exact, 0 sign flips, 0 different.
- Rows 217..219 are exactly 149^5110 - x245, x245^2 - x246, 149 x246^2 - x247. Only rows 61 and 219 contain x247.
- The text's claim that the starting system is "the first 216 rows of Section v19:250-rows, replacing the ladder coordinate x_250 by A": checked. The first 216 printed rows of the 250 table, with coordinate 250 replaced by A, equal the unbalanced 244 rows, and none contains coordinates 245..249.
- The committed input files (`explicit247-quadratic.json`, the normalization certificate, `unbalanced244-quadratic.json`) are byte-identical to Carbon's relay package.

## 3. Retained tables unchanged from Version 19

Sections `v19:195-rows` (958 lines), `v19:250-rows` (1,014 lines), `v19:195-maps`, `v19:250-maps` and `v19:contact-factors` are line-for-line identical between `quartic_v19.tex` and `quartic_v20.tex` in this root.

## 4. Source, PDF, build

- `research/version20/BUILD.json` (SHA-256 9811d542...): version 20, status success, source hash and PDF hash equal the files, pdf_bytes 5,170,658 equal the file, builder_sha256 5afbf705... equal to `research/version18/build_pdf.py`, three serial passes with return code 0, tex_errors 0, unresolved_references 0, auxiliary_stable true, 781 pages, title "Z is Diophantine in Q, Version 20".
- `scripts/check_current_manuscript.py`: exit status 0. `docs/current-manuscript.json` declares version 20 with those tex, pdf and build-record hashes and no extra inputs.
- PDF (pdfinfo, pdftotext): 781 pages; title as above; no `??`; no "working draft", "437 921" or "100 KB". First page shows Version 20, November 17, 2026, and the abstract with 247 variables, 3 385 monomials, coefficients below 2^73780, 96 712 bytes, 195 variables and 2 956 monomials.
- AI usage statement (TeX line 51529 and PDF last page): "... OpenAI Codex agents (6 Astra and 6.1 Sol), Anthropic Claude agents (Opus 5.5) and a Google Gemini agent (Gemini 4 Carbon), with auditing from Fable 5.1 and 5.2. ... analysis of the polynomials ...". In the TeX: "Gemini Carbon" 0 occurrences, "Gemini 4 Carbon" 4, "Astra 6" 0, "195-coordinate family" 0, "195-variable family" 0.
- Released manuscripts: `quartic_v16`, `v17`, `v18`, `v19` (.tex and .pdf, eight files) hash to the Git blobs at origin/main 3d2c9e56.
- `git diff origin/main -- scripts research/version18 research/version19 .github tests releases KERNEL_CONTRACT.json` is empty: builders, selector scripts and the Version 19 research folder are unchanged.

## 5. What the candidate changes relative to origin/main

Modified: `CITATION.bib`, `CREDITS.md`, `PROJECT.md`, `README.md`, `THIRD_PARTY_NOTICES.md`, `docs/current-manuscript.json`.
Added: `CURRENT_VERSION20.md`, `manuscripts/quartic_v20.tex`, `manuscripts/quartic_v20.pdf`, `research/version20/` (22 files).
Nothing under `.github/`, `scripts/`, `tests/`, `releases/`, and `KERNEL_CONTRACT.json` is untouched. Under the pending scope rule (PR 151) the Python and JSON files under `research/version20/` and `docs/current-manuscript.json` would not trigger a kernel build; the modified root files `CITATION.bib` (a .bib) and the .md files are documents.

## Observations (not mismatches)

- Version 19's PR also changed `docs/current-manuscript-build.md`, `docs/research-guide.md`, `manuscripts/README.md` and the research-checks workflow; this candidate does not (Astra says documentation and manifest updates are still in progress, and that CI still invokes the Version 19 checks). The new finite checks are therefore not run by CI in this PR.
- Outside the tables, the retained body (V20 from line 1459 against V19 from line 91) differs in 14 hunks, 55 lines. I did not review those edits; they are the corrections, which are the parent review's scope.
- The second-largest coefficient has 11,106 digits (the cross term with 149^5110), which is where most of the text size sits.

## Not checked

- The mathematical edits in the retained body (secant wording, scalar bound citation, deleted-coordinate explanation, formal-logarithm argument), `CORRECTIONS.md`, `DEPENDENCIES.md`, the release manifest and handoff files, and the modified root documents.
- The rendered PDF beyond text extraction (page images, table layout).
- I did not run pdfLaTeX or any build, and did not run the candidate's own check scripts.
- Carbon's obstruction remark at 246 (the draft makes no optimality claim).
- The printed 195 and 250 tables were compared with Version 19's text, not re-derived; they were verified against the data for Version 19.
