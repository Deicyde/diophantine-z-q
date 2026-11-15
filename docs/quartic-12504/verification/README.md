# Version 2 verification receipts

The released manuscript is `quartic_12504.tex`, SHA-256
`38d458ba4178083766c5ae56a894da595fe27170c1ef07f6b49750fc5edf7c37`.
Its PDF has SHA-256
`e747dcb58c541e5106ac6289cab660d624a7c1209b0e488aecc51ee8f54014b0`.

- [REPRODUCTION.json](REPRODUCTION.json) records 27 successful stages of
  frozen certificate replay and clean reconstruction. These include 38
  source-mutation cases, five resource-abort regressions, 30 malformed
  certificate cases, and the complete collected integer expansion.
- [INVENTORY.json](INVENTORY.json) records the final manuscript binding,
  443 unchanged historical application excerpts, 20 local lemmas, eleven
  inherited dependency families, and 92 evidence files. It checks the
  inventory's structure and exact text, not the truth of the theorems.
- [PDF_BUILD.json](PDF_BUILD.json) identifies the pinned compiler and TeX
  bundle, with no TeX errors or unresolved references.
- [PDF_VISUAL.json](PDF_VISUAL.json) records inspection of the title,
  contents, complete revised quartic section, final AI statement, and one
  inherited long display. The PDF has 186 pages.

The final edit displayed the source identifier on its own line. The
[layout addendum](../release-checks/LAYOUT_ADDENDUM.md) verifies that
reversing this formatting change reproduces the previously reviewed
arithmetic snippet byte for byte. The source system, certificate, and
coefficient table did not change.

The arithmetic and compiler reviews are in [reviews](https://github.com/elliotglazer/diophantine-z-q/tree/005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f/docs/quartic-12504/reviews) and
[release-checks](../release-checks/). These records distinguish mathematical
review, finite computation, document compilation, and archive integrity.
They do not claim a completed Lean proof or independent human peer review.
